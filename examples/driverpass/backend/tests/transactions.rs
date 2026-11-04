//! SQLite transaction tests for SR-001, SR-002 and SR-003.
//!
//! `formal/Transactions.lean` proves the transaction's step order correct
//! ASSUMING (A1) SQLite rolls back aborted transactions and (A2) `BEGIN
//! IMMEDIATE` serializes writers. These tests check A1 and A2, and the step
//! order itself, against a real SQLite database:
//!
//! * fault injection at every step: an aborted request changes nothing (A1);
//! * a committed request writes exactly one audit row (SR-003);
//! * many connections racing for one slot: exactly one wins (A2, SR-002);
//! * every request sequence up to length 4 over a small domain matches a
//!   reference model, the same fold over `allocate` as Lean's `run`.
//!
//! They are tests, not proofs: they cover the cases they run.

use driverpass_poc::domain::{allocate, Decision, Roster};
use driverpass_poc::service::{
    assign_slot_tx, configure, decision_name, initialize, load_roster, Fault, TxError, ALL_FAULTS,
};
use rusqlite::Connection;
use std::path::PathBuf;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc, Barrier,
};
use std::thread;

const INSTRUCTOR: i64 = 7;
const UNKNOWN: i64 = 99;

fn memory_db() -> Connection {
    let conn = Connection::open_in_memory().unwrap();
    initialize(&conn).unwrap();
    conn
}

/// A fresh database FILE (needed for multi-connection tests), under Cargo's
/// per-target temp directory, removed when dropped.
struct TempDb(PathBuf);

impl TempDb {
    fn new(name: &str) -> Self {
        static N: AtomicUsize = AtomicUsize::new(0);
        let n = N.fetch_add(1, Ordering::SeqCst);
        let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("{name}-{}-{n}.db", std::process::id()));
        let tmp = TempDb(path);
        tmp.cleanup();
        initialize(&tmp.open()).unwrap();
        tmp
    }
    fn open(&self) -> Connection {
        let conn = Connection::open(&self.0).unwrap();
        configure(&conn).unwrap();
        conn
    }
    fn cleanup(&self) {
        for ext in ["", "-wal", "-shm"] {
            let _ = std::fs::remove_file(format!("{}{ext}", self.0.display()));
        }
    }
}

impl Drop for TempDb {
    fn drop(&mut self) {
        self.cleanup();
    }
}

/// Everything a request may touch, for before/after comparison.
#[derive(Debug, PartialEq, Eq, Clone)]
struct Snapshot {
    instructors: Vec<(i64, i64)>,
    allocations: Vec<(i64, i64, i64)>,
    audit: Vec<(i64, i64, i64, String)>,
}

fn snapshot(conn: &Connection) -> Snapshot {
    fn rows<T>(conn: &Connection, sql: &str, f: impl Fn(&rusqlite::Row) -> rusqlite::Result<T>) -> Vec<T> {
        let mut stmt = conn.prepare(sql).unwrap();
        let out = stmt.query_map([], f).unwrap().collect::<rusqlite::Result<Vec<_>>>().unwrap();
        out
    }
    Snapshot {
        instructors: rows(conn, "SELECT id, off_duty FROM instructors ORDER BY id", |r| {
            Ok((r.get(0)?, r.get(1)?))
        }),
        allocations: rows(conn, "SELECT seq, instructor_id, slot_id FROM allocations ORDER BY seq", |r| {
            Ok((r.get(0)?, r.get(1)?, r.get(2)?))
        }),
        audit: rows(conn, "SELECT id, instructor_id, slot_id, decision FROM allocation_audit ORDER BY id", |r| {
            Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?))
        }),
    }
}

fn set_off_duty(conn: &Connection, off: bool) {
    conn.execute("UPDATE instructors SET off_duty = ?1 WHERE id = ?2", (i64::from(off), INSTRUCTOR))
        .unwrap();
}

// ------------------------------------------------------------ A1: rollback

#[test]
fn every_injected_fault_rolls_back_completely() {
    // Cover all three decisions: accepted (slot 5), duplicate (slot 1), off duty.
    for (off_duty, slot, expected) in [
        (false, 5, Decision::Accepted),
        (false, 1, Decision::Duplicate),
        (true, 5, Decision::OffDuty),
    ] {
        for fault in ALL_FAULTS {
            let mut conn = memory_db();
            assign_slot_tx(&mut conn, INSTRUCTOR, 1, None).unwrap();
            set_off_duty(&conn, off_duty);
            let before = snapshot(&conn);
            // Sanity: without a fault this request would be decided as `expected`.
            let mut probe = memory_db();
            assign_slot_tx(&mut probe, INSTRUCTOR, 1, None).unwrap();
            set_off_duty(&probe, off_duty);
            assert_eq!(assign_slot_tx(&mut probe, INSTRUCTOR, slot, None).unwrap().0, expected);

            let result = assign_slot_tx(&mut conn, INSTRUCTOR, slot, Some(fault));
            assert!(matches!(result, Err(TxError::Injected(f)) if f == fault), "{fault:?}: {result:?}");
            assert_eq!(snapshot(&conn), before, "{fault:?} on {expected:?} left a partial write");
        }
    }
}

#[test]
fn unknown_instructor_changes_nothing() {
    let mut conn = memory_db();
    let before = snapshot(&conn);
    assert!(matches!(assign_slot_tx(&mut conn, UNKNOWN, 3, None), Err(TxError::UnknownInstructor)));
    assert_eq!(snapshot(&conn), before);
}

// ------------------------------------------------------------ SR-003

#[test]
fn each_committed_request_audits_exactly_once() {
    let mut conn = memory_db();
    for (slot, expected) in [(4, Decision::Accepted), (4, Decision::Duplicate), (6, Decision::Accepted)] {
        let before = snapshot(&conn);
        let (decision, _) = assign_slot_tx(&mut conn, INSTRUCTOR, slot, None).unwrap();
        assert_eq!(decision, expected);
        let after = snapshot(&conn);
        assert_eq!(after.audit.len(), before.audit.len() + 1);
        let last = after.audit.last().unwrap();
        assert_eq!((last.1, last.2, last.3.as_str()), (INSTRUCTOR, slot, decision_name(decision)));
    }
}

// ------------------------------------------------------------ A2, SR-002

#[test]
fn concurrent_connections_never_double_book() {
    const THREADS: usize = 8;
    let db = Arc::new(TempDb::new("race"));
    let barrier = Arc::new(Barrier::new(THREADS));
    let handles: Vec<_> = (0..THREADS)
        .map(|_| {
            let (db, barrier) = (Arc::clone(&db), Arc::clone(&barrier));
            thread::spawn(move || {
                // Each thread has its OWN connection, so only SQLite's locking
                // (not the app's Mutex) keeps the requests apart.
                let mut conn = db.open();
                barrier.wait();
                assign_slot_tx(&mut conn, INSTRUCTOR, 42, None).map(|(d, _)| d)
            })
        })
        .collect();
    let decisions: Vec<Decision> =
        handles.into_iter().map(|h| h.join().unwrap().expect("no SQLITE_BUSY")).collect();
    let accepted = decisions.iter().filter(|d| **d == Decision::Accepted).count();
    assert_eq!(accepted, 1, "exactly one request may win slot 42: {decisions:?}");
    assert!(decisions.iter().all(|d| matches!(d, Decision::Accepted | Decision::Duplicate)));

    let conn = db.open();
    let snap = snapshot(&conn);
    assert_eq!(snap.allocations.len(), 1);
    assert_eq!(snap.audit.len(), THREADS, "every attempt is audited");
    assert_eq!(snap.audit.iter().filter(|a| a.3 == "accepted").count(), 1);
}

#[test]
fn concurrent_mixed_slots_keep_rosters_duplicate_free() {
    const THREADS: usize = 6;
    const PER_THREAD: i64 = 10;
    let db = Arc::new(TempDb::new("mixed"));
    let barrier = Arc::new(Barrier::new(THREADS));
    let handles: Vec<_> = (0..THREADS)
        .map(|t| {
            let (db, barrier) = (Arc::clone(&db), Arc::clone(&barrier));
            thread::spawn(move || {
                let mut conn = db.open();
                barrier.wait();
                // Overlapping requests: thread t asks for slots t%3 .. t%3+9.
                (0..PER_THREAD)
                    .map(|k| assign_slot_tx(&mut conn, INSTRUCTOR, (t as i64 % 3) + k, None).map(|(d, _)| d))
                    .collect::<Result<Vec<_>, _>>()
            })
        })
        .collect();
    let accepted: usize = handles
        .into_iter()
        .map(|h| h.join().unwrap().expect("no SQLITE_BUSY"))
        .map(|ds| ds.iter().filter(|d| **d == Decision::Accepted).count())
        .sum();

    let conn = db.open();
    let roster = load_roster(&conn, INSTRUCTOR).unwrap().unwrap();
    let mut unique = roster.slots.clone();
    unique.sort();
    unique.dedup();
    assert_eq!(unique.len(), roster.slots.len(), "double booking: {:?}", roster.slots);
    assert_eq!(unique, (0..12).collect::<Vec<_>>(), "slots 0..=11 are requested");
    assert_eq!(accepted, roster.slots.len(), "each acceptance stored exactly once");
    assert_eq!(snapshot(&conn).audit.len(), THREADS * PER_THREAD as usize);
}

// ------------------------------------------------------------ bounded sequences

#[derive(Debug, Clone, Copy)]
enum Req {
    Assign(i64, i64),
}

/// The reference: Lean's `DriverPassTx.run` without faults, over `allocate`.
fn reference(reqs: &[Req]) -> (Roster, Vec<Option<Decision>>, Vec<(i64, i64, String)>) {
    let mut roster = Roster { off_duty: false, slots: vec![] };
    let mut decisions = vec![];
    let mut audit = vec![];
    for Req::Assign(id, slot) in reqs.iter().copied() {
        if id != INSTRUCTOR {
            decisions.push(None);
            continue;
        }
        let (next, d) = allocate(&roster, slot);
        roster = next;
        decisions.push(Some(d));
        audit.push((id, slot, decision_name(d).to_owned()));
    }
    (roster, decisions, audit)
}

#[test]
fn all_request_sequences_up_to_length_4_match_reference() {
    let alphabet = [
        Req::Assign(INSTRUCTOR, 0),
        Req::Assign(INSTRUCTOR, 1),
        Req::Assign(INSTRUCTOR, 2),
        Req::Assign(UNKNOWN, 0),
    ];
    let mut sequences: Vec<Vec<Req>> = vec![vec![]];
    let mut frontier: Vec<Vec<Req>> = vec![vec![]];
    for _ in 0..4 {
        frontier = frontier
            .iter()
            .flat_map(|s| alphabet.iter().map(move |r| [s.clone(), vec![*r]].concat()))
            .collect();
        sequences.extend(frontier.iter().cloned());
    }
    assert_eq!(sequences.len(), 1 + 4 + 16 + 64 + 256);

    for seq in &sequences {
        let mut conn = memory_db();
        let mut decisions = vec![];
        for Req::Assign(id, slot) in seq.iter().copied() {
            decisions.push(match assign_slot_tx(&mut conn, id, slot, None) {
                Ok((d, _)) => Some(d),
                Err(TxError::UnknownInstructor) => None,
                Err(e) => panic!("{seq:?}: {e:?}"),
            });
        }
        let (want_roster, want_decisions, want_audit) = reference(seq);
        assert_eq!(decisions, want_decisions, "{seq:?}");
        assert_eq!(load_roster(&conn, INSTRUCTOR).unwrap().unwrap(), want_roster, "{seq:?}");
        let audit: Vec<_> = snapshot(&conn).audit.into_iter().map(|a| (a.1, a.2, a.3)).collect();
        assert_eq!(audit, want_audit, "{seq:?}");
    }
}

#[test]
fn faults_are_distinct_points() {
    // Guard: the Lean model and this test both rely on exactly four fault points.
    assert_eq!(ALL_FAULTS.len(), 4);
    assert_ne!(Fault::AfterRead, Fault::AtCommit);
}
