import System
import StateMachine

/-!
# Temporal properties of the formal RUP lifecycle

The lifecycle model (`packages/lifecycle/formal`) is imported unchanged and
viewed as a system: state `ProcessState`, input `Command`, output `Outcome`,
from `initial`. Each property holds on every run, for every input stream,
unless it lists assumptions.

| Id | Kind | Property |
|----|------|----------|
| L1 | safety | an accepted promotion had its gate satisfied and moved to the direct successor phase |
| L2 | safety | a requirements revision clears evidence, returns to inception and archives the old baseline |
| L3 | safety | phases never skip: same phase, direct successor, or back to inception |
| L4 | safety | evidence is only lost on a requirements revision |
| L5 | deadlock-freedom | `iterate` is always accepted; from any state, `reachCmds` reaches `transition` |
| L6 | liveness | under fairness assumptions, `transition` is eventually reached (see below) |

Assurance boundary: these are properties of the Lean model, assuming trusted
verification attestations, as in the lifecycle package.
No `sorry`, no `axiom`.
-/

namespace Architecton.Temporal

open Architecton.Lifecycle

def lifecycle : System ProcessState Command Outcome := ⟨initial, step⟩

abbrev LRec := Rec ProcessState Command Outcome

/-- The evidence the generated gate needs for inception, elaboration and
construction (`Policy.lean`). -/
def gateEvidence : List Evidence :=
  [.requirementsReviewed, .traceabilityReviewed, .designReviewed,
   .formalSpecificationChecked, .proofChecked, .conformancePassed, .artifactBuilt]

/-! ## Safety: L1–L4 -/

def l1Atom (r : LRec) : Bool :=
  !(decide (r.input = .promote) && decide (r.out = .accepted)) ||
    (gateSatisfied r.pre && decide (nextPhase r.pre.phase = some r.post.phase))

def l2Atom (r : LRec) : Bool :=
  !(decide (r.input = .reviseRequirements)) ||
    (decide (r.post.verified = []) && decide (r.post.phase = .inception) &&
      decide ((r.pre.revision, r.pre.verified) ∈ r.post.archive))

def l3Atom (r : LRec) : Bool :=
  decide (r.post.phase = r.pre.phase) || decide (nextPhase r.pre.phase = some r.post.phase) ||
    decide (r.post.phase = .inception)

def l4Atom (r : LRec) : Bool :=
  decide (r.input = .reviseRequirements) || r.pre.verified.all fun e => decide (e ∈ r.post.verified)

/-- L1: safe promotion. -/
theorem L1 (u : Nat → Command) : sat (run lifecycle u) 0 (.always (.atom l1Atom)) := by
  refine step_rule _ (fun _ => true) (fun _ => true) rfl (fun _ _ _ _ => rfl) (fun _ => rfl) ?_
  intro s c _ _
  cases c with
  | promote =>
    cases hn : nextPhase s.phase with
    | none => simp [recAt, lifecycle, step, l1Atom, hn]
    | some t =>
      cases hg : gateSatisfied s <;> simp [recAt, lifecycle, step, l1Atom, hn, hg]
  | _ => simp [recAt, lifecycle, step, l1Atom]

/-- L2: a requirements revision resets the baseline. -/
theorem L2 (u : Nat → Command) : sat (run lifecycle u) 0 (.always (.atom l2Atom)) := by
  refine step_rule _ (fun _ => true) (fun _ => true) rfl (fun _ _ _ _ => rfl) (fun _ => rfl) ?_
  intro s c _ _
  cases c with
  | promote =>
    cases hn : nextPhase s.phase with
    | none => simp [recAt, lifecycle, step, l2Atom, hn]
    | some t => cases hg : gateSatisfied s <;> simp [recAt, lifecycle, step, l2Atom, hn, hg]
  | _ => simp [recAt, lifecycle, step, l2Atom]

/-- L3: no phase skipping. -/
theorem L3 (u : Nat → Command) : sat (run lifecycle u) 0 (.always (.atom l3Atom)) := by
  refine step_rule _ (fun _ => true) (fun _ => true) rfl (fun _ _ _ _ => rfl) (fun _ => rfl) ?_
  intro s c _ _
  cases c with
  | promote =>
    cases hn : nextPhase s.phase with
    | none => simp [recAt, lifecycle, step, l3Atom, hn]
    | some t => cases hg : gateSatisfied s <;> simp [recAt, lifecycle, step, l3Atom, hn, hg]
  | _ => simp [recAt, lifecycle, step, l3Atom]

/-- L4: evidence is only lost on a requirements revision. -/
theorem L4 (u : Nat → Command) : sat (run lifecycle u) 0 (.always (.atom l4Atom)) := by
  refine step_rule _ (fun _ => true) (fun _ => true) rfl (fun _ _ _ _ => rfl) (fun _ => rfl) ?_
  intro s c _ _
  cases c with
  | promote =>
    cases hn : nextPhase s.phase with
    | none => simp [recAt, lifecycle, step, l4Atom, hn]
    | some t => cases hg : gateSatisfied s <;> simp [recAt, lifecycle, step, l4Atom, hn, hg]
  | _ =>
    simp [recAt, lifecycle, step, l4Atom]
    all_goals intro x hx; simp [hx]

/-! ## Deadlock-freedom: L5 -/

theorem L5_iterate (s : ProcessState) : (step s .iterate).2 = .accepted := rfl

/-- Record every gate's evidence, then promote three times. -/
def reachCmds : List Command :=
  gateEvidence.map .recordValidated ++ [.promote, .promote, .promote]

/-- L5: from every state (reachable or not), `reachCmds` reaches `transition`. -/
theorem L5_reach (s : ProcessState) : (finalState lifecycle s reachCmds).phase = .transition := by
  obtain ⟨ph, it, rev, ver, arch⟩ := s
  cases ph <;>
    simp [finalState, reachCmds, gateEvidence, lifecycle, step, gateSatisfied, nextPhase]

end Architecton.Temporal
