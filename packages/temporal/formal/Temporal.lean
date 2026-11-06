/-!
# Linear temporal logic with two semantics

`LTL α` is a deep embedding of linear temporal logic over trace elements of
type `α`. Atoms are Boolean predicates, so the finite evaluator is decidable.

* `sat w i φ` is the standard semantics over an infinite trace `w : Nat → α`.
* `satF w i φ` is the finite-trace semantics (LTLf) over `w : List α`:
  - a position `i ≥ w.length` is outside the trace, and atoms are false there;
  - `next` is *strong*: at the last position `next φ` is false, while the
    derived weak next `wnext φ` is true;
  - `until` only looks at positions inside the trace.

`satF` uses structural recursion only, so `decide` evaluates it in the kernel.
Plain Lean 4 core, no Mathlib; no `sorry`, no `axiom`.
-/

namespace Architecton.Temporal

inductive LTL (α : Type) where
  | tt
  | atom (p : α → Bool)
  | not (φ : LTL α)
  | and (φ ψ : LTL α)
  | or (φ ψ : LTL α)
  | next (φ : LTL α)
  | until (φ ψ : LTL α)

namespace LTL

variable {α : Type}

def ff : LTL α := not tt
def imp (φ ψ : LTL α) : LTL α := or (not φ) ψ
/-- ◇ φ -/
def eventually (φ : LTL α) : LTL α := .until tt φ
/-- □ φ -/
def always (φ : LTL α) : LTL α := not (eventually (not φ))
/-- weak next: true at the end of a finite trace -/
def wnext (φ : LTL α) : LTL α := not (next (not φ))
/-- weak until: φ U ψ, or φ forever -/
def wuntil (φ ψ : LTL α) : LTL α := or (.until φ ψ) (always φ)
/-- conjunction of a list of formulas -/
def all : List (LTL α) → LTL α
  | [] => tt
  | φ :: φs => and φ (all φs)

end LTL

variable {α : Type}

/-- Infinite-trace semantics. -/
def sat (w : Nat → α) : Nat → LTL α → Prop
  | _, .tt => True
  | i, .atom p => p (w i) = true
  | i, .not φ => ¬ sat w i φ
  | i, .and φ ψ => sat w i φ ∧ sat w i ψ
  | i, .or φ ψ => sat w i φ ∨ sat w i ψ
  | i, .next φ => sat w (i + 1) φ
  | i, .until φ ψ => ∃ k, i ≤ k ∧ sat w k ψ ∧ ∀ j, i ≤ j → j < k → sat w j φ

/-- Scan positions `i, i+1, …` for at most `fuel` steps: some position
satisfies `g`, and every earlier one satisfies `f`. -/
def untilF (f g : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => false
  | i, fuel + 1 => g i || (f i && untilF f g (i + 1) fuel)

/-- Finite-trace semantics (LTLf). -/
def satF (w : List α) : Nat → LTL α → Bool
  | _, .tt => true
  | i, .atom p => match w[i]? with
    | some x => p x
    | none => false
  | i, .not φ => !satF w i φ
  | i, .and φ ψ => satF w i φ && satF w i ψ
  | i, .or φ ψ => satF w i φ || satF w i ψ
  | i, .next φ => decide (i + 1 < w.length) && satF w (i + 1) φ
  | i, .until φ ψ => untilF (fun j => satF w j φ) (fun j => satF w j ψ) i (w.length - i)

end Architecton.Temporal
