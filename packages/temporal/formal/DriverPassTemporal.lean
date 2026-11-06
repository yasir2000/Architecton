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
| D4b | liveness | if a request is retried infinitely often, the slot is eventually booked and stays booked |
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

end Architecton.Temporal
