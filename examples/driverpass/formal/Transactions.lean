import DriverPass

/-!
SQLite transaction model of `POST /api/v1/instructors/{id}/slots`
(backend/src/service.rs `assign_slot_tx`), for SR-001, SR-002 and SR-003.

The model follows the code's steps inside one `BEGIN IMMEDIATE` transaction:
read the roster, decide with `allocate`, insert the allocation if accepted,
insert the audit row, commit. A `Fault` aborts at one of those points.

TRUSTED ASSUMPTIONS (not proved here; they are SQLite's job):
* A1 (atomicity): an aborted transaction leaves the database exactly as it was.
  The model encodes this by returning the original `db` on every fault.
* A2 (isolation): `BEGIN IMMEDIATE` takes the write lock before the read, so
  concurrent requests take effect one at a time, in some order. Any
  concurrent run is therefore modelled as `run` over SOME list of requests.
The Rust tests in backend/tests/transactions.rs exercise A1 and A2 against a
real SQLite database; they are tests, not proofs.

No `sorry`, no `axiom`.
-/

namespace DriverPassTx

structure Db where
  /-- instructor id and off-duty flag -/
  instructors : List (Nat × Bool)
  /-- (instructor, slot), newest first, like `ORDER BY seq DESC` -/
  allocations : List (Nat × Nat)
  /-- (instructor, slot, decision), newest first -/
  audit : List (Nat × Nat × Decision)
  deriving DecidableEq, Repr

/-- The roster the code reads with `load_roster`. -/
def slotsOf (allocs : List (Nat × Nat)) (i : Nat) : List Nat :=
  (allocs.filter (fun p => p.1 == i)).map (·.2)

def roster (db : Db) (i : Nat) : Option Roster :=
  (db.instructors.lookup i).map fun off => ⟨off, slotsOf db.allocations i⟩

inductive Fault where
  | afterRead | afterAllocationInsert | afterAuditInsert | atCommit
  deriving DecidableEq, Repr

inductive Response where
  | decided (d : Decision) (r : Roster)
  | unknownInstructor
  | databaseError
  deriving DecidableEq, Repr

/-- One request, step by step as the code runs it. Every abort returns the
original `db` (assumption A1). -/
def assignTx (db : Db) (i slot : Nat) (fault : Option Fault) : Db × Response :=
  match roster db i with
  | none => (db, .unknownInstructor)
  | some cur =>
    if fault = some .afterRead then (db, .databaseError) else
    let r := allocate cur slot
    let db1 := if r.2 = .accepted then { db with allocations := (i, slot) :: db.allocations } else db
    if fault = some .afterAllocationInsert then (db, .databaseError) else
    let db2 := { db1 with audit := (i, slot, r.2) :: db1.audit }
    if fault = some .afterAuditInsert then (db, .databaseError) else
    if fault = some .atCommit then (db, .databaseError) else
    (db2, .decided r.2 r.1)

/-! ## One transaction -/

/-- All or nothing: unless the request was decided, nothing changed. -/
theorem tx_all_or_nothing (db : Db) (i slot : Nat) (f : Option Fault) :
    (∃ d r, (assignTx db i slot f).2 = .decided d r) ∨ (assignTx db i slot f).1 = db := by
  unfold assignTx
  split
  · simp
  · repeat (first | split | simp)

/-- A failed request (any fault) changes nothing. -/
theorem tx_fault_rolls_back (db : Db) (i slot : Nat) (f : Fault) :
    (assignTx db i slot (some f)).1 = db := by
  unfold assignTx
  split
  · rfl
  · cases f <;> simp

/-- SR-003: a committed request for a known instructor adds exactly one audit
row, recording the decision `allocate` made. -/
theorem tx_audits_exactly_once (db : Db) (i slot : Nat) (cur : Roster)
    (h : roster db i = some cur) :
    (assignTx db i slot none).1.audit = (i, slot, (allocate cur slot).2) :: db.audit := by
  unfold assignTx
  rw [h]
  by_cases ha : (allocate cur slot).2 = .accepted <;> simp [ha]

/-- SR-001 at database level: when `allocate` rejects, no allocation is
inserted, whatever fault occurs. -/
theorem tx_rejected_keeps_allocations (db : Db) (i slot : Nat) (f : Option Fault)
    (cur : Roster) (h : roster db i = some cur) (hd : (allocate cur slot).2 ≠ .accepted) :
    (assignTx db i slot f).1.allocations = db.allocations := by
  unfold assignTx
  rw [h]
  cases f with
  | none => simp [hd]
  | some f => cases f <;> simp

theorem slotsOf_cons_same (allocs : List (Nat × Nat)) (i slot : Nat) :
    slotsOf ((i, slot) :: allocs) i = slot :: slotsOf allocs i := by
  simp [slotsOf]

theorem slotsOf_cons_other (allocs : List (Nat × Nat)) {i j : Nat} (slot : Nat) (h : j ≠ i) :
    slotsOf ((i, slot) :: allocs) j = slotsOf allocs j := by
  simp [slotsOf, Ne.symm h]

/-- The HTTP response carries exactly `allocate`'s decision and roster. -/
theorem tx_response (db : Db) (i slot : Nat) (cur : Roster) (h : roster db i = some cur) :
    (assignTx db i slot none).2 = .decided (allocate cur slot).2 (allocate cur slot).1 := by
  unfold assignTx
  rw [h]
  by_cases ha : (allocate cur slot).2 = .accepted <;> simp [ha]

/-- The roster in the HTTP response is exactly the roster now stored: the API
never reports a state the database does not hold. -/
theorem tx_response_matches_store (db : Db) (i slot : Nat) (cur : Roster)
    (h : roster db i = some cur) :
    roster (assignTx db i slot none).1 i = some (allocate cur slot).1 := by
  have hcur := h
  simp only [roster, Option.map_eq_some_iff] at hcur
  obtain ⟨off, hoff, rfl⟩ := hcur
  unfold assignTx
  rw [h]
  cases off with
  | true => simp [allocate, roster, hoff]
  | false =>
      by_cases hm : slot ∈ slotsOf db.allocations i
      · simp [allocate, hm, roster, hoff]
      · simp [allocate, hm, roster, hoff, slotsOf_cons_same]

/-! ## Any serial order of requests (assumption A2) -/

def nodupNat : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupNat xs

/-- No instructor holds the same slot twice. Depends on allocations only. -/
def AllocOk (as : List (Nat × Nat)) : Prop := ∀ j, nodupNat (slotsOf as j) = true

def NoDoubleBooking (db : Db) : Prop := AllocOk db.allocations

/-- A request either leaves the allocations alone, or prepends exactly the
requested slot after `allocate` accepted it on the roster it read. -/
theorem tx_allocations (db : Db) (i slot : Nat) (f : Option Fault) :
    (assignTx db i slot f).1.allocations = db.allocations ∨
    ∃ cur, roster db i = some cur ∧ (allocate cur slot).2 = .accepted ∧
      (assignTx db i slot f).1.allocations = (i, slot) :: db.allocations := by
  unfold assignTx
  split
  · exact Or.inl rfl
  · next cur hcur =>
      by_cases ha : (allocate cur slot).2 = .accepted
      · cases f with
        | none => exact Or.inr ⟨cur, hcur, ha, by simp [ha]⟩
        | some f => exact Or.inl (by cases f <;> simp)
      · exact Or.inl (by cases f with
          | none => simp [ha]
          | some f => cases f <;> simp)

theorem tx_preserves_no_double_booking (db : Db) (i slot : Nat) (f : Option Fault)
    (h : NoDoubleBooking db) : NoDoubleBooking (assignTx db i slot f).1 := by
  unfold NoDoubleBooking
  rcases tx_allocations db i slot f with h1 | ⟨cur, hcur, ha, h1⟩
  · rw [h1]; exact h
  · rw [h1]
    simp only [roster, Option.map_eq_some_iff] at hcur
    obtain ⟨off, -, rfl⟩ := hcur
    cases off with
    | true => simp [allocate] at ha
    | false =>
        by_cases hm : slot ∈ slotsOf db.allocations i
        · simp [allocate, hm] at ha
        · intro j
          by_cases hj : j = i
          · subst hj
            simpa [slotsOf_cons_same, nodupNat, hm] using h j
          · simpa [slotsOf_cons_other _ _ hj] using h j

/-- A serial execution: each request runs to completion before the next. -/
def run (db : Db) : List (Nat × Nat × Option Fault) → Db
  | [] => db
  | (i, slot, f) :: rest => run (assignTx db i slot f).1 rest

/-- SR-002's goal: under serial execution, in ANY order and with ANY faults,
no instructor is ever double-booked. -/
theorem run_no_double_booking (db : Db) (reqs : List (Nat × Nat × Option Fault))
    (h : NoDoubleBooking db) : NoDoubleBooking (run db reqs) := by
  induction reqs generalizing db with
  | nil => exact h
  | cons req rest ih =>
      obtain ⟨i, slot, f⟩ := req
      exact ih _ (tx_preserves_no_double_booking db i slot f h)

/-! ## Why the lock matters -/

/-- Without `BEGIN IMMEDIATE`, two requests could both read the roster before
either writes (a lost update), then both insert. -/
def racyPair (db : Db) (i slot : Nat) : Db :=
  match roster db i with
  | none => db
  | some cur =>
    let d1 := (allocate cur slot).2   -- request 1 reads and decides
    let d2 := (allocate cur slot).2   -- request 2 reads the SAME snapshot
    let add (d : Decision) (as : List (Nat × Nat)) := if d = .accepted then (i, slot) :: as else as
    { db with allocations := add d2 (add d1 db.allocations) }

def demo : Db := { instructors := [(7, false)], allocations := [], audit := [] }

/-- The interleaving the lock rules out really does double-book. (The
`UNIQUE(instructor_id, slot_id)` constraint is a second line of defence.) -/
theorem racy_interleaving_double_books :
    slotsOf (racyPair demo 7 42).allocations 7 = [42, 42] := by decide

/-- The same two requests run serially: the second is rejected. -/
theorem serial_pair_rejects_second :
    slotsOf (run demo [(7, 42, none), (7, 42, none)]).allocations 7 = [42] := by decide

end DriverPassTx
