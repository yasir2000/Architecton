import Temporal
import Bridge

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

end Architecton.Temporal.Examples
