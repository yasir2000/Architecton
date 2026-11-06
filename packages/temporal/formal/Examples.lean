import Temporal
import Bridge
import System
import LifecycleTemporal
import DriverPassTemporal

/-! Decide-checked examples and sanity runs for the temporal core. -/

open Architecton.Temporal

namespace Architecton.Temporal.Examples

/-! ## Finite semantics: one passing and one failing case per operator -/

example : satF [1,2,3] 0 (.always (.atom (· > 0))) = true := by decide
example : satF [1,2,3] 0 (.always (.atom (· > 1))) = false := by decide
example : satF [1,2,3] 0 (.eventually (.atom (· = 3))) = true := by decide
example : satF [1,2,3] 0 (.eventually (.atom (· = 4))) = false := by decide
example : satF [1,1,2] 0 (.until (.atom (· = 1)) (.atom (· = 2))) = true := by decide
example : satF [1,3,2] 0 (.until (.atom (· = 1)) (.atom (· = 2))) = false := by decide
example : satF [1] 0 (.next .tt) = false := by decide      -- strong next at the end
example : satF [1] 0 (.wnext .ff) = true := by decide      -- weak next at the end
example : satF ([] : List Nat) 0 (.atom (fun _ => true)) = false := by decide
example : satF ([] : List Nat) 0 (.always (.atom (fun _ => false))) = true := by decide
example : satF [1,2] 0 (.wuntil (.atom (· < 5)) (.atom (· = 9))) = true := by decide

/-! ## Bridge between the semantics -/

example : Safe (.always (.atom (fun n : Nat => decide (n > 0)))) := by repeat constructor
example (w : Nat → Nat) (h : ∀ k, w k > 0) : satF (prefixOf w 5) 0 (.always (.atom (· > 0))) = true :=
  safe_prefix (by repeat constructor) ((sat_always_iff).2 fun j _ => by simp [sat_atom_iff, h]) (by decide)
example : satF [3,1,2] 0 (.always (.atom (· > 0))) = [3,1,2].all (· > 0) := satF_always_atom

/-! ## Systems, runs and proof rules, on a counter -/

def ctr : System Nat Bool Unit := ⟨0, fun s b => (if b then s + 1 else s, ())⟩

example : (runF ctr 0 [true, false, true]).map (·.post) = [1, 1, 2] := by decide
example (u : Nat → Bool) : sat (runFrom ctr 0 u) 0 (.always (.atom fun r => decide (r.pre ≤ r.post))) :=
  step_rule _ (fun _ => true) (fun _ => true) rfl (fun _ _ _ _ => rfl) (fun _ => rfl)
    (by intro s b _ _; cases b <;> simp [recAt, ctr])
example (u : Nat → Bool) (h : ∀ n, ∃ m ≥ n, u m = true) :
    sat (runFrom ctr 0 u) 0 (infOften (.atom fun r => r.input)) :=
  sat_infOften_atom_iff.2 (by simpa [runFrom, recAt] using h)

/-! ## Lifecycle: the antecedents of L1, L2 and L5 actually occur -/

open Architecton.Lifecycle in
example : (runF lifecycle initial (reachCmds ++ [.reviseRequirements])).any
    (fun r => r.input == .promote && r.out == .accepted) = true := by decide
open Architecton.Lifecycle in
example : (runF lifecycle initial (reachCmds ++ [.reviseRequirements])).any
    (fun r => r.input == .reviseRequirements) = true := by decide
open Architecton.Lifecycle in
example : (runF lifecycle initial (reachCmds ++ [.reviseRequirements])).all l2Atom = true := by decide
open Architecton.Lifecycle in
example : (finalState lifecycle initial reachCmds).phase = .transition := L5_reach _

/-! ## Lifecycle liveness: L6 applies to a concrete fair stream -/

example : sat (run lifecycle uFair) 0 (.eventually (.atom atTransition)) :=
  L6 uFair uFair_assumptions.1 uFair_assumptions.2.1 uFair_assumptions.2.2
#check @L6_needs_no_revise
#check @L6_needs_promote
#check @L6_needs_evidence

/-! ## DriverPass: the antecedents of D2, D3 and D4a actually occur -/

open DriverPassTx in
def dpReqs : List Req := [(7, 42, none), (7, 42, none), (7, 43, some .atCommit), (9, 1, none)]
example : (runF driverpass DriverPassTx.demo dpReqs).all d3Atom = true := by decide
example : (runF driverpass DriverPassTx.demo dpReqs).any (fun r => !isDecided r.out) = true := by decide
example : (runF driverpass DriverPassTx.demo dpReqs).any
    (fun r => r.out matches .decided .accepted _) = true := by decide
example : (runF driverpass DriverPassTx.demo dpReqs).all d2Atom = true := by decide
#check @D5_extensions

end Architecton.Temporal.Examples
