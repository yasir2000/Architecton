//! Transactional service layer: the SQLite side of `POST .../slots`.
//!
//! Modelled in Lean by `formal/Transactions.lean` (`DriverPassTx.assignTx`),
//! step for step: read the roster, decide with the generated `allocate`,
//! insert the allocation if accepted, insert the audit row, commit, all inside
//! ONE `BEGIN IMMEDIATE` transaction (SR-002, SR-003).
//!
//! `fault` exists only so tests can abort at each step and check that SQLite
//! rolls everything back. The HTTP handler always passes `None`.
use crate::domain::{allocate, Decision, Roster};
use rusqlite::{params, Connection, OptionalExtension, TransactionBehavior};

/// Points at which a test can abort the transaction. Mirrors `DriverPassTx.Fault`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fault {
    AfterRead,
    AfterAllocationInsert,
    AfterAuditInsert,
    AtCommit,
}

pub const ALL_FAULTS: [Fault; 4] = [
    Fault::AfterRead,
    Fault::AfterAllocationInsert,
    Fault::AfterAuditInsert,
    Fault::AtCommit,
];

#[derive(Debug)]
pub enum TxError {
    UnknownInstructor,
    Database(rusqlite::Error),
    /// A test-injected abort. The transaction was rolled back.
    Injected(Fault),
}

impl From<rusqlite::Error> for TxError {
    fn from(e: rusqlite::Error) -> Self {
        TxError::Database(e)
    }
}

/// Per-connection settings. Every connection must call this, because
/// `busy_timeout` is per connection: without it, a concurrent writer fails
/// with SQLITE_BUSY instead of waiting for the lock.
pub fn configure(conn: &Connection) -> rusqlite::Result<()> {
    conn.execute_batch(
        "PRAGMA foreign_keys=ON;
         PRAGMA journal_mode=WAL;
         PRAGMA synchronous=FULL;
         PRAGMA busy_timeout=5000;",
    )
}

pub fn initialize(conn: &Connection) -> rusqlite::Result<()> {
    configure(conn)?;
    conn.execute_batch(
        "CREATE TABLE IF NOT EXISTS instructors (
            id INTEGER PRIMARY KEY CHECK(id >= 0),
            off_duty INTEGER NOT NULL CHECK(off_duty IN (0,1))
         );
         CREATE TABLE IF NOT EXISTS allocations (
            seq INTEGER PRIMARY KEY AUTOINCREMENT,
            instructor_id INTEGER NOT NULL REFERENCES instructors(id),
            slot_id INTEGER NOT NULL CHECK(slot_id >= 0),
            UNIQUE(instructor_id, slot_id)
         );
         CREATE TABLE IF NOT EXISTS allocation_audit (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            instructor_id INTEGER NOT NULL REFERENCES instructors(id),
            slot_id INTEGER NOT NULL CHECK(slot_id >= 0),
            decision TEXT NOT NULL CHECK(decision IN ('accepted','off_duty','duplicate')),
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
         );
         INSERT OR IGNORE INTO instructors(id, off_duty) VALUES (7, 0);",
    )
}

pub fn load_roster(db: &Connection, instructor_id: i64) -> rusqlite::Result<Option<Roster>> {
    let duty: Option<i64> = db
        .query_row(
            "SELECT off_duty FROM instructors WHERE id = ?1",
            [instructor_id],
            |row| row.get(0),
        )
        .optional()?;
    let Some(duty) = duty else { return Ok(None) };
    let mut stmt = db.prepare(
        "SELECT slot_id FROM allocations WHERE instructor_id = ?1 ORDER BY seq DESC",
    )?;
    let slots = stmt
        .query_map([instructor_id], |row| row.get::<_, i64>(0))?
        .collect::<rusqlite::Result<Vec<_>>>()?;
    Ok(Some(Roster { off_duty: duty != 0, slots }))
}

pub fn decision_name(decision: Decision) -> &'static str {
    match decision {
        Decision::Accepted => "accepted",
        Decision::OffDuty => "off_duty",
        Decision::Duplicate => "duplicate",
    }
}

fn inject(fault: Option<Fault>, here: Fault) -> Result<(), TxError> {
    if fault == Some(here) {
        Err(TxError::Injected(here))
    } else {
        Ok(())
    }
}

/// Assign `slot` to instructor `id` in one IMMEDIATE transaction. On any error
/// the transaction is dropped without commit, which rolls it back.
pub fn assign_slot_tx(
    conn: &mut Connection,
    id: i64,
    slot: i64,
    fault: Option<Fault>,
) -> Result<(Decision, Roster), TxError> {
    // IMMEDIATE takes the write lock BEFORE the read, so no other writer can
    // change the roster between our read and our write (SR-002).
    let tx = conn.transaction_with_behavior(TransactionBehavior::Immediate)?;
    let current = load_roster(&tx, id)?.ok_or(TxError::UnknownInstructor)?;
    inject(fault, Fault::AfterRead)?;
    let (next, decision) = allocate(&current, slot);
    if decision == Decision::Accepted {
        tx.execute(
            "INSERT INTO allocations(instructor_id, slot_id) VALUES (?1, ?2)",
            params![id, slot],
        )?;
    }
    inject(fault, Fault::AfterAllocationInsert)?;
    // SR-003: every decided attempt for a known instructor is audited, in the
    // same transaction as its effect.
    tx.execute(
        "INSERT INTO allocation_audit(instructor_id, slot_id, decision) VALUES (?1, ?2, ?3)",
        params![id, slot, decision_name(decision)],
    )?;
    inject(fault, Fault::AfterAuditInsert)?;
    inject(fault, Fault::AtCommit)?;
    tx.commit()?;
    Ok((decision, next))
}
