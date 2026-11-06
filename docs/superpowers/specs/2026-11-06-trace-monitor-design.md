# Runtime trace monitor: design

Date: 2026-11-06. Status: approved in conversation, awaiting written-spec review.
Sub-project 2 of the temporal/runtime verification work package (sub-project 1:
[temporal core](2026-11-06-temporal-core-design.md)).

## Goal

An **offline checker** that takes the DriverPass service's SQLite database (or an
exported trace) and decides whether its logs are a run of the Lean model, and whether
they satisfy the safety formulas proved in `packages/temporal`. The formulas checked are
the same Lean terms the theorems are about, evaluated with the same `satF`.

Success: a log produced by the real service passes; each hand-made faulty log fails the
intended check at the intended event; three soundness theorems connect the verdicts to the
temporal core; the whole thing runs in CI and in the evidence ledger.

Non-goals: online monitoring inside the service; lifecycle evidence logs; concurrency or
distributed consistency beyond assumption A2; monitoring from a mid-life snapshot.

## Decisions taken

| Question | Decision |
|---|---|
| Purpose | offline checker (CLI, CI, evidence ledger); no code in the request path |
| Duty changes | the service logs them in a new `duty_audit` table, so `off_duty` decisions are checkable |
| Implementation | Python stdlib extractor → `trace.json` → Lean checker run with `lean --run` (core `Lean.Data.Json`, no Mathlib) |

Feasibility probe: `lean --run` with `import Lean.Data.Json` on v4.35.0 parses a JSON
file in about 11 s, dominated by import loading.

## 1. Service change (`examples/driverpass/backend`)

New table, created by `initialize`:

```sql
CREATE TABLE IF NOT EXISTS duty_audit (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  instructor_id INTEGER NOT NULL REFERENCES instructors(id),
  off_duty INTEGER NOT NULL CHECK(off_duty IN (0,1)),
  after_audit_id INTEGER NOT NULL CHECK(after_audit_id >= 0),
  created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
);
```

The duty update moves from `main.rs` into `service::set_duty_tx(conn, id, off_duty)`. Inside
the existing `IMMEDIATE` transaction it updates `instructors` and inserts one `duty_audit` row
with `after_audit_id = COALESCE((SELECT MAX(id) FROM allocation_audit), 0)`. An unknown
instructor changes nothing and writes no row. `PATCH /duty` calls it. `allocation_audit` is
unchanged.

**Order.** Writers are serialised (A2), so a duty row with `after_audit_id = k` happened
after allocation audit row `k` and before row `k+1`. Duty rows with equal `after_audit_id`
keep their `id` order. This gives a total order over both logs.

Rust tests (`tests/transactions.rs`): a duty change writes exactly one row with the right
`after_audit_id`; an unknown instructor writes none; interleaved assignments and duty
changes produce rows whose merged order is the execution order. A scenario test writes a
real database file and exports it as the fixture `packages/temporal/monitor/fixtures/good.json`
(through the extractor), so the "good" fixture comes from the service, not by hand.

## 2. Trace format and extractor

`packages/temporal/monitor/extract_trace.py`, stdlib only (`sqlite3`, `json`), opens the
database read-only and writes:

```json
{ "version": 1,
  "init":   { "instructors": [[7, false]] },
  "events": [ {"kind": "assign", "id": 1, "instructor": 7, "slot": 3, "decision": "accepted"},
              {"kind": "duty",   "id": 1, "instructor": 7, "off_duty": true} ],
  "final":  { "instructors": [[7, true]], "allocations": [[7, 3]] } }
```

* `init` is the seeded state of `service::initialize`, the same as Lean `demo`
  (instructor 7, on duty, nothing allocated). Monitoring starts from the seed.
* `events` merges both tables in the order of section 1.
* `final` is the live `instructors` and `allocations` tables.
* Errors (exit 2): file missing, tables missing, unknown `decision` value, or a `version`
  the checker does not know.

## 3. Lean model extension (`packages/temporal/formal/DriverPassOps.lean`)

```lean
inductive Ev | assign (i slot : Nat) | duty (i : Nat) (off : Bool)
def setDuty (db : Db) (i : Nat) (off : Bool) : Db × Response  -- unknown → (db, .unknownInstructor)
def driverpassOps : System Db Ev Response  -- init := demo; assign uses assignTx db i slot none
theorem D1_ops (db0) (h : NoDoubleBooking db0) (u : Nat → Ev) :
  sat (runFrom driverpassOps db0 u) 0 (.always (.atom fun r => allocOkB r.post))
```

`Transactions.lean` and `DriverPassTemporal.lean` are imported unchanged. A duty change
leaves `allocations` untouched, so `D1_ops` follows from `tx_preserves_no_double_booking`
by `step_rule`.

## 4. Checker (`formal/Monitor.lean`, `monitor/Main.lean`)

**Observed trace.** States are rebuilt from the logged effects, never from the model's
decisions: an `assign i s d` event adds the audit row `(i, s, d)` and, if
`d = accepted`, the allocation `(i, s)` (newest first, as in `Db`); a `duty i off` event sets
the flag. Each event yields a record `⟨pre, ev, post⟩` (type `Rec Db Ev LoggedOut`).

**Checks.** Each check reports the index of the first failing event (M4: the trace length).

| Id | Check | Catches |
|---|---|---|
| M1 | conformance: the instructor is known in `pre`, and for `assign` the logged decision equals `(allocate cur slot).2` with `cur = roster pre i` | wrong accept/duplicate/off-duty decisions, rows for unknown instructors |
| M2 | `satF` of `□ (atom fun r => allocOkB r.post)` (D1's formula) | double booking, judged on the observed states alone |
| M3 | `satF` of `□ (atom fun r => r.pre.allocations.all (· ∈ r.post.allocations))` (the growth half of D2) | lost allocations |
| M4 | the rebuilt final instructors and allocations equal `final`, as sets | a log that disagrees with the data, e.g. an unaudited write |

M2 and M3 are in the `Safe` fragment. M2 and M3 are evaluated on the whole trace; the first
violating index is found by evaluating `satF` on growing prefixes.

**Theorems** (all in the axiom audit, with `D1_ops`):

* `conforms_is_run`: if M1 passes on events `evs`, the observed record trace equals
  `runF driverpassOps demo (inputs evs)` on states and inputs. Hence every model theorem
  (`D1_ops`, D2, D3) holds for this log.
* `violation_real`: if M2 or M3 fails on the observed trace, no infinite trace extending it
  satisfies the formula (contrapositive of `safe_prefix`).
* `reject_sound`: if M1 first fails at event `k`, no run of `driverpassOps` from `demo`
  on the logged inputs yields the logged decisions for events `0..k`.

**Report** (stdout, one JSON line):
`{"verdict": "conforms"|"violation", "checks": {"M1": true, ...},
"first_violation": {"check": "M2", "index": 4, "reason": "..."} | null}`.
Exit codes: 0 conforms, 1 violation, 2 malformed input.

## 5. CLI

`python packages/temporal/monitor/check_trace.py <db-or-trace.json>`: runs the extractor if
given a `.db`, then `lean --run monitor/Main.lean trace.json` with the toolchain pinned
by `ELAN_TOOLCHAIN` and `LEAN_PATH` set to the built modules (as `scripts/verify.py`).
It passes the exit code through.

## 6. Testing

* Rust: the `duty_audit` tests and the fixture-producing scenario of section 1.
* Python (unittest, `packages/temporal/tests`): extractor ordering (duty rows between the
  right audit rows, ties by `id`), empty logs, missing tables, unknown decision, version
  check; `check_trace.py` exit-code passthrough.
* Lean `decide` examples (`formal/Examples.lean`): one conforming trace and one trace failing
  each of M1–M4, with the expected index.
* Fixtures `monitor/fixtures/bad-m1.json` … `bad-m4.json` (hand-made) and `good.json` (from
  the service). A test runs the checker on each: `good` gives exit 0; each `bad-mN` gives
  exit 1 with `first_violation.check = "MN"` at the stated index.
* Non-vacuity: every check fails on some fixture, and `good` exercises all three decisions
  and at least one duty change.

## 7. CI, evidence, docs

* `scripts/verify.py` also builds `DriverPassOps` and `Monitor`; `check_axioms.REQUIRED`
  adds `D1_ops`, `conforms_is_run`, `violation_real`, `reject_sound`.
* `verify-temporal.yml` runs the fixture test after `verify.py`.
* `evidence/checks.json`: a new check `temporal-monitor`, `depends_on: ["temporal-lean"]`.
* Docs: a Monitor section in `packages/temporal/README.md` (and fix its stale
  "19 theorems" line); roadmap in the root `README.md`; `docs/assurance.md`; `CHANGELOG.md`.

## Assurance boundary

* The checker judges **logs**, not the running service. A write that is neither audited nor
  visible in the final tables is invisible to it.
* The merged order relies on `after_audit_id`, which is correct under A2 (serialised writers).
* Monitoring starts from the seeded state; a database seeded differently is reported by M4
  or M1, not silently accepted.
* Faulted (rolled-back) requests leave no rows, consistent with D2 and A1; the checker cannot
  see them and does not need to.
* The Lean checker is trusted to be the program it appears to be: its verdict functions are
  the ones the theorems are about, but the JSON parsing and the `lean --run` interpreter are
  outside the proofs.
