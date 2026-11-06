import System
import Transactions

/-!
# Temporal properties of the DriverPass slot service

The SQLite transaction model (`examples/driverpass/formal/Transactions.lean`)
is imported unchanged and viewed as a system: state `Db`, input
`(instructor, slot, fault)`, output `Response`. Runs start from any database
`db0`; theorems that need it assume `NoDoubleBooking db0`.

| Id | Kind | Property |
|----|------|----------|
| D1 | safety | no instructor is ever double-booked, for any request and fault stream |
| D2 | safety | a request that is not decided changes nothing; allocations only grow |
| D3 | response | a fault-free request for a known instructor is decided and audited exactly once, in the same step |
| D4a | progress | an on-duty instructor's fault-free request for a free slot is accepted |
| D4b | liveness | once a fault-free request is made, the slot is booked and stays booked (`D4b_once`); the spec's retry-fairness form follows (`D4b`) |
| D5 | violation | the lost-update interleaving violates D1's formula on a two-state trace, and so on every continuation |

Assurance boundary: properties of the Lean model, under the model's
assumptions A1 (atomicity) and A2 (serial execution under `BEGIN IMMEDIATE`).
No `sorry`, no `axiom`.
-/

namespace Architecton.Temporal

open DriverPassTx

abbrev Req := Nat × Nat × Option Fault

def driverpass : System Db Req Response := ⟨demo, fun db r => assignTx db r.1 r.2.1 r.2.2⟩

abbrev DRec := Rec Db Req Response

/-! ## D1: no double booking on every run -/

/-- Boolean form of `NoDoubleBooking`, usable as an atom. -/
def allocOkB (db : Db) : Bool :=
  db.allocations.all fun a => nodupNat (slotsOf db.allocations a.1)

theorem slotsOf_eq_nil {as : List (Nat × Nat)} {j : Nat} (h : ∀ a ∈ as, a.1 ≠ j) :
    slotsOf as j = [] := by
  unfold slotsOf
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro a ha
  simpa using h a ha

theorem allocOkB_iff {db : Db} : allocOkB db = true ↔ NoDoubleBooking db := by
  unfold allocOkB NoDoubleBooking AllocOk
  rw [List.all_eq_true]
  constructor
  · intro h j
    by_cases hj : ∃ a ∈ db.allocations, a.1 = j
    · obtain ⟨a, ha, rfl⟩ := hj
      exact h a ha
    · rw [slotsOf_eq_nil fun a ha hj' => hj ⟨a, ha, hj'⟩]
      rfl
  · intro h a _
    exact h a.1

theorem D1 (db0 : Db) (h : NoDoubleBooking db0) (u : Nat → Req) :
    sat (runFrom driverpass db0 u) 0 (.always (.atom fun r => allocOkB r.post)) := by
  have pres : ∀ s q, allocOkB s = true → allocOkB (driverpass.step s q).1 = true :=
    fun s q hs => allocOkB_iff.2 (tx_preserves_no_double_booking s _ _ _ (allocOkB_iff.1 hs))
  exact step_rule _ allocOkB (fun _ => true) (allocOkB_iff.2 h) (fun s q _ hs => pres s q hs)
    (fun _ => rfl) (fun s q _ hs => pres s q hs)

/-! ## D2: all or nothing; allocations only grow -/

def isDecided : Response → Bool
  | .decided _ _ => true
  | _ => false

def d2Atom (r : DRec) : Bool :=
  (isDecided r.out || decide (r.post = r.pre)) &&
    r.pre.allocations.all fun a => decide (a ∈ r.post.allocations)

theorem tx_not_decided (db : Db) (i slot : Nat) (f : Option Fault)
    (h : isDecided (assignTx db i slot f).2 = false) : (assignTx db i slot f).1 = db := by
  unfold assignTx at h ⊢
  cases hr : roster db i with
  | none => rfl
  | some cur =>
    simp only [hr] at h ⊢
    cases f with
    | some f => cases f <;> simp
    | none =>
      by_cases ha : (allocate cur slot).2 = .accepted <;> simp [ha, isDecided] at h

theorem tx_alloc_mono (db : Db) (i slot : Nat) (f : Option Fault) :
    ∀ a ∈ db.allocations, a ∈ (assignTx db i slot f).1.allocations := by
  intro a ha
  rcases tx_allocations db i slot f with h | ⟨_, _, _, h⟩
  · rw [h]; exact ha
  · rw [h]; exact List.mem_cons_of_mem _ ha

theorem D2 (db0 : Db) (u : Nat → Req) :
    sat (runFrom driverpass db0 u) 0 (.always (.atom d2Atom)) := by
  refine step_rule _ (fun _ => true) (fun _ => true) rfl (fun _ _ _ _ => rfl) (fun _ => rfl) ?_
  intro s q _ _
  obtain ⟨i, slot, f⟩ := q
  simp only [d2Atom, recAt, driverpass, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true]
  refine ⟨?_, fun a ha => decide_eq_true (tx_alloc_mono s i slot f a ha)⟩
  cases hd : isDecided (assignTx s i slot f).2
  · exact Or.inr (decide_eq_true (tx_not_decided s i slot f hd))
  · exact Or.inl rfl

/-! ## D3: response -/

def d3Atom (r : DRec) : Bool :=
  !((roster r.pre r.input.1).isSome && decide (r.input.2.2 = none)) ||
    match r.out with
    | .decided d _ => decide (r.post.audit = (r.input.1, r.input.2.1, d) :: r.pre.audit)
    | _ => false

theorem D3 (db0 : Db) (u : Nat → Req) :
    sat (runFrom driverpass db0 u) 0 (.always (.atom d3Atom)) := by
  refine step_rule _ (fun _ => true) (fun _ => true) rfl (fun _ _ _ _ => rfl) (fun _ => rfl) ?_
  intro s q _ _
  obtain ⟨i, slot, f⟩ := q
  cases hr : roster s i with
  | none => simp [d3Atom, recAt, hr]
  | some cur =>
    cases f with
    | some f => simp [d3Atom, recAt, hr]
    | none =>
      by_cases ha : (allocate cur slot).2 = .accepted <;>
        simp [d3Atom, recAt, driverpass, assignTx, hr, ha]

/-! ## D4a: progress -/

theorem roster_slots {db : Db} {i : Nat} {r : Roster} (h : roster db i = some r) :
    r.slots = slotsOf db.allocations i := by
  unfold roster at h
  cases hl : db.instructors.lookup i with
  | none => simp [hl] at h
  | some off => simp [hl] at h; rw [← h]

theorem D4a (db : Db) (i slot : Nat) (r : Roster) (hr : roster db i = some r)
    (hon : r.offDuty = false) (hfree : slot ∉ slotsOf db.allocations i) :
    ∃ r', (assignTx db i slot none).2 = .decided .accepted r' := by
  have hnot : slot ∉ r.slots := by rw [roster_slots hr]; exact hfree
  simp [assignTx, hr, allocate, hon, hnot]

/-! ## D5: the race, as a temporal violation -/

/-- The state before and after the lost-update interleaving. -/
def racyTrace : List Db := [demo, racyPair demo 7 42]

theorem D5 : satF racyTrace 0 (.always (.atom allocOkB)) = false := by decide

/-- Every infinite state sequence that starts with the racy trace violates
`□ allocOkB`: a finite violation of a safe formula is final. -/
theorem D5_extensions (w : Nat → Db) (h : prefixOf w 2 = racyTrace) :
    ¬ sat w 0 (.always (.atom allocOkB)) := by
  intro hs
  have := safe_prefix (Safe.always (Safe.atom _)) hs (n := 2) (by decide)
  rw [h, D5] at this
  exact Bool.false_ne_true this

/-! ## D4b: a booking request eventually lands and persists -/

theorem instructors_stable (db : Db) (q : Req) :
    (driverpass.step db q).1.instructors = db.instructors := by
  obtain ⟨i, slot, f⟩ := q
  show (assignTx db i slot f).1.instructors = db.instructors
  unfold assignTx
  cases hr : roster db i with
  | none => rfl
  | some cur =>
    simp only
    cases f with
    | some f => cases f <;> simp
    | none => by_cases ha : (allocate cur slot).2 = .accepted <;> simp [ha]

theorem mem_slotsOf {as : List (Nat × Nat)} {i slot : Nat} :
    slot ∈ slotsOf as i ↔ (i, slot) ∈ as := by
  unfold slotsOf
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨j, s⟩, ⟨h, rfl⟩, rfl⟩; exact h
  · intro h; exact ⟨(i, slot), ⟨h, rfl⟩, rfl⟩

theorem roster_lookup {db : Db} {i : Nat} {r : Roster} (h : roster db i = some r) :
    db.instructors.lookup i = some r.offDuty := by
  unfold roster at h
  cases hl : db.instructors.lookup i with
  | none => simp [hl] at h
  | some off => simp [hl] at h; rw [← h]

/-- A fault-free request by an on-duty instructor books the slot: it is
accepted, or the slot was already booked. -/
theorem request_books (db : Db) (i slot : Nat) (cur : Roster) (hr : roster db i = some cur)
    (hon : cur.offDuty = false) : (i, slot) ∈ (assignTx db i slot none).1.allocations := by
  have hs := roster_slots hr
  by_cases hin : slot ∈ cur.slots
  · simp [assignTx, hr, allocate, hon, hin]
    rw [hs] at hin
    exact mem_slotsOf.1 hin
  · simp [assignTx, hr, allocate, hon, hin]

/-- D4b, sharpest form: a single fault-free request by an on-duty instructor
books the slot for good, whatever faults or other requests come before or
after it. -/
theorem D4b_once (db0 : Db) (i slot : Nat) (r0 : Roster) (hr : roster db0 i = some r0)
    (hon : r0.offDuty = false) (u : Nat → Req) (hone : ∃ m, u m = (i, slot, none)) :
    sat (runFrom driverpass db0 u) 0
      (.eventually (.always (.atom fun r => (slotsOf r.post.allocations i).contains slot))) := by
  -- the instructor list never changes, so `i` stays known and on duty
  have hlook : ∀ n, (statesFrom driverpass db0 u n).instructors.lookup i = some false := by
    intro n
    induction n with
    | zero => rw [← hon]; exact roster_lookup hr
    | succ n ih => show (driverpass.step _ _).1.instructors.lookup i = _; rw [instructors_stable]; exact ih
  have hros : ∀ n, roster (statesFrom driverpass db0 u n) i =
      some ⟨false, slotsOf (statesFrom driverpass db0 u n).allocations i⟩ := by
    intro n; unfold roster; rw [hlook n]; rfl
  obtain ⟨m, hm⟩ := hone
  have hbook : (i, slot) ∈ (statesFrom driverpass db0 u (m + 1)).allocations := by
    show (i, slot) ∈ (driverpass.step (statesFrom driverpass db0 u m) (u m)).1.allocations
    rw [hm]
    exact request_books _ i slot _ (hros m) rfl
  -- allocations only grow (D2), so the booking persists
  have hkeep : ∀ k, (i, slot) ∈ (statesFrom driverpass db0 u (m + 1 + k)).allocations := by
    intro k
    induction k with
    | zero => exact hbook
    | succ k ih =>
      rw [← Nat.add_assoc]
      exact tx_alloc_mono (statesFrom driverpass db0 u (m + 1 + k)) _ _ _ _ ih
  refine sat_eventually_always_iff.2 ⟨m, fun n hn => ?_⟩
  show (slotsOf (statesFrom driverpass db0 u (n + 1)).allocations i).contains slot = true
  have := hkeep (n - m)
  rw [show m + 1 + (n - m) = n + 1 by omega] at this
  simpa using mem_slotsOf.2 this

/-- D4b as stated in the spec, with retry fairness. Retrying infinitely often
is more than needed: by `D4b_once`, one fault-free request is enough. -/
theorem D4b (db0 : Db) (i slot : Nat) (r0 : Roster) (hr : roster db0 i = some r0)
    (hon : r0.offDuty = false) (u : Nat → Req) (hinf : ∀ n, ∃ m ≥ n, u m = (i, slot, none)) :
    sat (runFrom driverpass db0 u) 0
      (.eventually (.always (.atom fun r => (slotsOf r.post.allocations i).contains slot))) :=
  let ⟨m, _, hm⟩ := hinf 0
  D4b_once db0 i slot r0 hr hon u ⟨m, hm⟩

end Architecton.Temporal
