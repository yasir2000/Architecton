import DriverPassIR
import Step
import DriverPass

/-!
IR ↔ Lean refinement for DriverPass. Hand-written; checked against the
generated IR model (`DriverPassIR`) and the generated Lean specification
(`DriverPass`).

* `ir_refines_allocate`: for EVERY roster and slot, running the IR transition
  `TR-assign_slot` on the encoded roster gives exactly the encoded result of
  `allocate`. The IR is therefore not merely anchored to `allocate`; it
  computes the same function.
* `allocate_preserves_nodup` and `ir_preserves_inv001`: invariant INV-001
  (an instructor never holds a slot twice) is preserved by every step.

No `sorry`, no `axiom`.
-/

open Architecton.IR

namespace DriverPassConformance

/-- How a Lean `Roster` is represented as an IR state. -/
def encode (s : Roster) : Env :=
  [("offDuty", .bool s.offDuty), ("slots", .natList s.slots)]

/-- How a Lean `Decision` is named as an IR outcome. -/
def outcomeName : Decision → String
  | .accepted => "accepted"
  | .offDuty => "off_duty"
  | .duplicate => "duplicate"

def params (slot : Nat) : Env := [("slot", .nat slot)]

/-- The IR transition, taken from the generated model, not retyped. -/
def assignTr : Transition :=
  match driverPass.transitions with
  | tr :: _ => tr
  | [] => { id := "", params := [], guards := [], otherwiseRequirement := "",
            otherwiseOutcome := "", effect := [] }

theorem assignTr_mem : assignTr ∈ driverPass.transitions := by decide

theorem encode_conforms (s : Roster) : Conforms driverPass.stateVars (encode s) := by
  intro n t h
  simp only [driverPass, List.lookup] at h
  split at h
  · next he => simp at he h; subst he; subst h; exact ⟨_, rfl, rfl⟩
  · split at h
    · next _ he => simp at he h; subst he; subst h; exact ⟨_, rfl, rfl⟩
    · simp at h

theorem params_conforms (slot : Nat) : Conforms assignTr.params (params slot) := by
  intro n t h
  simp only [assignTr, driverPass, List.lookup] at h
  split at h
  · next he => simp at he h; subst he; subst h; exact ⟨_, rfl, rfl⟩
  · simp at h

/-- The IR transition computes `allocate`, for all inputs. -/
theorem ir_refines_allocate (s : Roster) (slot : Nat) :
    step assignTr (encode s) (params slot) =
      some (encode (allocate s slot).1, outcomeName (allocate s slot).2) := by
  obtain ⟨off, slots⟩ := s
  cases off with
  | true =>
      simp [step, assignTr, driverPass, fireGuards, eval, encode, params, allocate,
        outcomeName, List.lookup]
  | false =>
      by_cases hm : slot ∈ slots
      · simp [step, assignTr, driverPass, fireGuards, eval, encode, params, allocate,
          outcomeName, List.lookup, hm]
      · simp [step, assignTr, driverPass, fireGuards, eval, evalEffect, writeAll,
          Env.set, encode, params, allocate, outcomeName, List.lookup, hm]

/-- INV-001 holds after `allocate` whenever it held before. -/
theorem allocate_preserves_nodup (s : Roster) (slot : Nat)
    (h : distinctNat s.slots = true) : distinctNat (allocate s slot).1.slots = true := by
  obtain ⟨off, slots⟩ := s
  cases off with
  | true => simpa [allocate] using h
  | false =>
      by_cases hm : slot ∈ slots
      · simpa [allocate, hm] using h
      · simpa [allocate, hm, distinctNat] using h

/-- The IR's own invariant body, evaluated on the encoded state. -/
theorem inv001_body : driverPass.invariants.map (·.body) = [.nodup (.var "slots")] := by
  decide

theorem eval_inv001 (s : Roster) :
    eval (encode s) [] (.nodup (.var "slots")) = some (.bool (distinctNat s.slots)) := by
  simp [eval, encode, List.lookup]

/-- INV-001, stated on the IR: if the invariant holds in the encoded state,
it holds in the state the IR transition produces. -/
theorem ir_preserves_inv001 (s : Roster) (slot : Nat)
    (h : eval (encode s) [] (.nodup (.var "slots")) = some (.bool true)) :
    ∃ σ' o, step assignTr (encode s) (params slot) = some (σ', o) ∧
      eval σ' [] (.nodup (.var "slots")) = some (.bool true) := by
  rw [eval_inv001] at h
  simp only [Option.some.injEq, Val.bool.injEq] at h
  refine ⟨encode (allocate s slot).1, outcomeName (allocate s slot).2,
    ir_refines_allocate s slot, ?_⟩
  rw [eval_inv001, allocate_preserves_nodup s slot h]

/-- The general progress theorem, instantiated: the DriverPass transition
never gets stuck on any roster. (Also implied by `ir_refines_allocate`.) -/
theorem assign_progress (s : Roster) (slot : Nat) :
    ∃ r, step assignTr (encode s) (params slot) = some r :=
  step_progress driverPass_wellFormed assignTr_mem (encode_conforms s) (params_conforms slot)

end DriverPassConformance
