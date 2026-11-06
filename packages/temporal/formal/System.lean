import Bridge

/-!
# Step-function systems, runs, proof rules and fairness

The Architecton models are deterministic step functions with an output,
`step : σ → ι → σ × ο`. A run is driven by an input stream `u : Nat → ι`; each
trace position is a transition record `⟨pre, input, post, out⟩`, so formulas
can refer to commands and outcomes as well as states.

Proof rules let instance files prove temporal properties without unfolding
`sat`. Fairness is stated as LTL assumptions on the input stream: the models
are driven by their environment, so fairness is something the environment
promises, not something the system guarantees.

No `sorry`, no `axiom`.
-/

namespace Architecton.Temporal

structure System (σ ι ο : Type) where
  init : σ
  step : σ → ι → σ × ο

/-- One transition: state before, input, state after, output. -/
structure Rec (σ ι ο : Type) where
  pre : σ
  input : ι
  post : σ
  out : ο

variable {σ ι ο : Type}

def recAt (sys : System σ ι ο) (s : σ) (i : ι) : Rec σ ι ο :=
  ⟨s, i, (sys.step s i).1, (sys.step s i).2⟩

/-- State before step `n`, starting from `s`. -/
def statesFrom (sys : System σ ι ο) (s : σ) (u : Nat → ι) : Nat → σ
  | 0 => s
  | n + 1 => (sys.step (statesFrom sys s u n) (u n)).1

/-- The record trace of the run from `s` driven by `u`. -/
def runFrom (sys : System σ ι ο) (s : σ) (u : Nat → ι) : Nat → Rec σ ι ο :=
  fun n => recAt sys (statesFrom sys s u n) (u n)

def run (sys : System σ ι ο) (u : Nat → ι) : Nat → Rec σ ι ο :=
  runFrom sys sys.init u

/-- The finite record trace for a list of inputs. -/
def runF (sys : System σ ι ο) (s : σ) : List ι → List (Rec σ ι ο)
  | [] => []
  | i :: is => recAt sys s i :: runF sys (sys.step s i).1 is

/-- The state after a list of inputs. -/
def finalState (sys : System σ ι ο) (s : σ) : List ι → σ
  | [] => s
  | i :: is => finalState sys (sys.step s i).1 is

theorem runFrom_link (sys : System σ ι ο) (s : σ) (u : Nat → ι) (n : Nat) :
    (runFrom sys s u (n + 1)).pre = (runFrom sys s u n).post := rfl

theorem runF_range' (sys : System σ ι ο) (s : σ) (u : Nat → ι) (n k : Nat) :
    runF sys (statesFrom sys s u k) ((List.range' k n).map u) =
      (List.range' k n).map (runFrom sys s u) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [List.range'_succ, List.map_cons, runF]
    rw [← ih (k + 1)]
    rfl

/-- The finite run on the first `n` inputs is the length-`n` prefix of the
infinite run. -/
theorem runF_prefix (sys : System σ ι ο) (s : σ) (u : Nat → ι) (n : Nat) :
    runF sys s ((List.range n).map u) = prefixOf (runFrom sys s u) n := by
  have := runF_range' sys s u n 0
  simp only [statesFrom] at this
  simpa [prefixOf, List.range_eq_range'] using this

/-! ## Proof rules -/

/-- Invariant rule: `P` holds initially and is preserved by every step whose
input is `Good`; on an input stream of `Good` inputs it holds at every state. -/
theorem invariant_rule {sys : System σ ι ο} {s : σ} {u : Nat → ι}
    (P : σ → Bool) (Good : ι → Bool) (h0 : P s = true)
    (hstep : ∀ s i, Good i = true → P s = true → P (sys.step s i).1 = true)
    (hu : ∀ n, Good (u n) = true) : ∀ n, P (statesFrom sys s u n) = true := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hstep _ _ (hu n) ih

/-- Step rule: if every `Good` step from a `P`-state satisfies `Q`, then
`□ Q` holds on the record trace. With `P` and `Good` constantly true this is
an unconditional property of single steps. -/
theorem step_rule {sys : System σ ι ο} {s : σ} {u : Nat → ι}
    (Q : Rec σ ι ο → Bool) (P : σ → Bool) (Good : ι → Bool) (h0 : P s = true)
    (hstep : ∀ s i, Good i = true → P s = true → P (sys.step s i).1 = true)
    (hu : ∀ n, Good (u n) = true)
    (hq : ∀ s i, Good i = true → P s = true → Q (recAt sys s i) = true) :
    sat (runFrom sys s u) 0 (.always (.atom Q)) :=
  sat_always_iff.2 fun j _ => hq _ _ (hu j) (invariant_rule P Good h0 hstep hu j)

/-- Ranking rule: a measure that never increases from `n0` on, strictly
decreases on helpful steps while positive, with helpful steps infinitely
often, reaches zero; `goal` holds wherever it is zero. -/
theorem ranking_rule (r : Nat → Rec σ ι ο) (hlink : ∀ n, (r (n + 1)).pre = (r n).post)
    (μ : σ → Nat) (helpful goal : Rec σ ι ο → Bool) (n0 : Nat)
    (hmono : ∀ n ≥ n0, μ (r n).post ≤ μ (r n).pre)
    (hdec : ∀ n ≥ n0, helpful (r n) = true → 0 < μ (r n).pre → μ (r n).post < μ (r n).pre)
    (hinf : ∀ n, ∃ m ≥ n, helpful (r m) = true)
    (hgoal : ∀ n, μ (r n).pre = 0 → goal (r n) = true) :
    sat r 0 (.eventually (.atom goal)) := by
  -- the measure never increases along the trace from n0
  have chain : ∀ n ≥ n0, ∀ k, μ (r (n + k)).pre ≤ μ (r n).pre := by
    intro n hn k
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      rw [← Nat.add_assoc, hlink]
      exact Nat.le_trans (hmono _ (by omega)) ih
  have reach : ∀ v, ∀ n ≥ n0, μ (r n).pre ≤ v → ∃ m ≥ n, μ (r m).pre = 0 := by
    intro v
    induction v using Nat.strongRecOn with
    | _ v ih =>
      intro n hn hv
      by_cases h0 : μ (r n).pre = 0
      · exact ⟨n, Nat.le_refl _, h0⟩
      obtain ⟨m, hm, hh⟩ := hinf n
      have hle : μ (r m).pre ≤ μ (r n).pre := by
        have := chain n hn (m - n)
        rwa [Nat.add_sub_cancel' hm] at this
      by_cases hm0 : μ (r m).pre = 0
      · exact ⟨m, hm, hm0⟩
      have hlt := hdec m (by omega) hh (by omega)
      rw [← hlink] at hlt
      obtain ⟨m', hm', h'⟩ :=
        ih (μ (r (m + 1)).pre) (by omega) (m + 1) (by omega) (Nat.le_refl _)
      exact ⟨m', by omega, h'⟩
  obtain ⟨m, _, hm⟩ := reach _ n0 (Nat.le_refl _) (Nat.le_refl _)
  exact sat_eventually_iff.2 ⟨m, Nat.zero_le _, hgoal m hm⟩

/-! ## Fairness, as assumptions on the trace -/

variable {α : Type}

/-- □◇ φ -/
def infOften (φ : LTL α) : LTL α := .always (.eventually φ)

/-- Weak fairness: continuously enabled from some point on implies taken
infinitely often. -/
def WF (en tk : LTL α) : LTL α := .imp (.eventually (.always en)) (.always (.eventually tk))

/-- Strong fairness: enabled infinitely often implies taken infinitely often. -/
def SF (en tk : LTL α) : LTL α := .imp (.always (.eventually en)) (.always (.eventually tk))

theorem sat_infOften_atom_iff {w : Nat → α} {p : α → Bool} :
    sat w 0 (infOften (.atom p)) ↔ ∀ n, ∃ m ≥ n, p (w m) = true := by
  unfold infOften
  rw [sat_always_iff]
  constructor
  · intro h n
    obtain ⟨m, hm, hp⟩ := sat_eventually_iff.1 (h n (Nat.zero_le _))
    exact ⟨m, hm, hp⟩
  · intro h n _
    obtain ⟨m, hm, hp⟩ := h n
    exact sat_eventually_iff.2 ⟨m, hm, hp⟩

theorem sat_eventually_always_iff {w : Nat → α} {φ : LTL α} :
    sat w 0 (.eventually (.always φ)) ↔ ∃ T, ∀ n ≥ T, sat w n φ := by
  rw [sat_eventually_iff]
  constructor
  · rintro ⟨T, _, h⟩; exact ⟨T, sat_always_iff.1 h⟩
  · rintro ⟨T, h⟩; exact ⟨T, Nat.zero_le _, sat_always_iff.2 h⟩

theorem sat_WF_atom_iff {w : Nat → α} {en tk : α → Bool} :
    sat w 0 (WF (.atom en) (.atom tk)) ↔
      ((∃ T, ∀ n ≥ T, en (w n) = true) → ∀ n, ∃ m ≥ n, tk (w m) = true) := by
  have h : sat w 0 (infOften (.atom tk)) ↔ _ := sat_infOften_atom_iff
  unfold infOften at h
  unfold WF
  rw [sat_imp_iff, sat_eventually_always_iff, h]
  exact Iff.rfl

theorem sat_SF_atom_iff {w : Nat → α} {en tk : α → Bool} :
    sat w 0 (SF (.atom en) (.atom tk)) ↔
      ((∀ n, ∃ m ≥ n, en (w m) = true) → ∀ n, ∃ m ≥ n, tk (w m) = true) := by
  have he : sat w 0 (infOften (.atom en)) ↔ _ := sat_infOften_atom_iff
  have ht : sat w 0 (infOften (.atom tk)) ↔ _ := sat_infOften_atom_iff
  unfold infOften at he ht
  unfold SF
  rw [sat_imp_iff, he, ht]

end Architecton.Temporal
