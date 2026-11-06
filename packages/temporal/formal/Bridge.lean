import Temporal

/-!
# Linking the infinite and finite semantics

* `safe_prefix`: a formula in the syntactic safety fragment that holds on an
  infinite trace holds on every non-empty finite prefix of it. Read backwards,
  this is what makes a runtime monitor sound: a finite log that violates a
  safe formula is violated by every infinite continuation of that log.
* `cosafe_prefix`: a formula in the co-safety fragment that holds on a finite
  prefix holds on the infinite trace, so a finite witness proves an
  eventuality.

Also: characterisation lemmas for both semantics, used by the proof rules.
No `sorry`, no `axiom`.
-/

namespace Architecton.Temporal

variable {α : Type}

/-! ## Prefixes -/

/-- The first `n` elements of an infinite trace. -/
def prefixOf (w : Nat → α) (n : Nat) : List α := (List.range n).map w

@[simp] theorem prefix_length (w : Nat → α) (n : Nat) : (prefixOf w n).length = n := by
  simp [prefixOf]

theorem prefix_getElem? (w : Nat → α) (n i : Nat) :
    (prefixOf w n)[i]? = if i < n then some (w i) else none := by
  by_cases h : i < n <;> simp [prefixOf, h]

theorem prefix_get (w : Nat → α) {n i : Nat} (h : i < n) : (prefixOf w n)[i]? = some (w i) := by
  simp only [prefix_getElem?, h, ite_true]

/-! ## Infinite semantics: characterisations -/

theorem sat_atom_iff {w : Nat → α} {i : Nat} {p : α → Bool} :
    sat w i (.atom p) ↔ p (w i) = true := Iff.rfl

theorem sat_and_iff {w : Nat → α} {i : Nat} {φ ψ : LTL α} :
    sat w i (.and φ ψ) ↔ sat w i φ ∧ sat w i ψ := Iff.rfl

theorem sat_or_iff {w : Nat → α} {i : Nat} {φ ψ : LTL α} :
    sat w i (.or φ ψ) ↔ sat w i φ ∨ sat w i ψ := Iff.rfl

theorem sat_imp_iff {w : Nat → α} {i : Nat} {φ ψ : LTL α} :
    sat w i (.imp φ ψ) ↔ (sat w i φ → sat w i ψ) := by
  show (¬ sat w i φ ∨ sat w i ψ) ↔ _
  constructor
  · rintro (h | h) hφ
    · exact absurd hφ h
    · exact h
  · intro h
    by_cases hφ : sat w i φ
    · exact Or.inr (h hφ)
    · exact Or.inl hφ

theorem sat_eventually_iff {w : Nat → α} {i : Nat} {φ : LTL α} :
    sat w i (.eventually φ) ↔ ∃ j, i ≤ j ∧ sat w j φ := by
  show (∃ k, i ≤ k ∧ sat w k φ ∧ ∀ j, i ≤ j → j < k → True) ↔ _
  constructor
  · rintro ⟨k, hk, h, _⟩; exact ⟨k, hk, h⟩
  · rintro ⟨k, hk, h⟩; exact ⟨k, hk, h, fun _ _ _ => trivial⟩

theorem sat_always_iff {w : Nat → α} {i : Nat} {φ : LTL α} :
    sat w i (.always φ) ↔ ∀ j, i ≤ j → sat w j φ := by
  show ¬ sat w i (.eventually (.not φ)) ↔ _
  rw [sat_eventually_iff]
  constructor
  · intro h j hj
    by_cases hφ : sat w j φ
    · exact hφ
    · exact absurd ⟨j, hj, hφ⟩ h
  · rintro h ⟨j, hj, hn⟩
    exact hn (h j hj)

theorem sat_wnext_iff {w : Nat → α} {i : Nat} {φ : LTL α} :
    sat w i (.wnext φ) ↔ sat w (i + 1) φ := by
  show ¬ ¬ sat w (i + 1) φ ↔ _
  exact ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

theorem sat_until_iff {w : Nat → α} {i : Nat} {φ ψ : LTL α} :
    sat w i (.until φ ψ) ↔ ∃ k, i ≤ k ∧ sat w k ψ ∧ ∀ j, i ≤ j → j < k → sat w j φ :=
  Iff.rfl

/-- `□` is `¬◇¬`, by definition, in both semantics. -/
theorem sat_not_eventually_not {w : Nat → α} {i : Nat} {φ : LTL α} :
    sat w i (.not (.eventually (.not φ))) ↔ sat w i (.always φ) := Iff.rfl

/-! ## Finite semantics: characterisations -/

theorem untilF_iff (f g : Nat → Bool) (fuel i : Nat) :
    untilF f g i fuel = true ↔
      ∃ k, i ≤ k ∧ k < i + fuel ∧ g k = true ∧ ∀ j, i ≤ j → j < k → f j = true := by
  induction fuel generalizing i with
  | zero => simp [untilF]; intro k hk hk'; omega
  | succ n ih =>
    simp only [untilF, Bool.or_eq_true, Bool.and_eq_true, ih]
    constructor
    · rintro (hg | ⟨hf, k, hk, hkn, hgk, hj⟩)
      · exact ⟨i, Nat.le_refl _, by omega, hg, fun j h1 h2 => by omega⟩
      · refine ⟨k, by omega, by omega, hgk, fun j h1 h2 => ?_⟩
        by_cases hji : j = i
        · subst hji; exact hf
        · exact hj j (by omega) h2
    · rintro ⟨k, hk, hkn, hgk, hj⟩
      by_cases hki : k = i
      · subst hki; exact Or.inl hgk
      · exact Or.inr ⟨hj i (Nat.le_refl _) (by omega),
          k, by omega, by omega, hgk, fun j h1 h2 => hj j (by omega) h2⟩

theorem satF_atom_lt {w : List α} {i : Nat} {p : α → Bool} (h : i < w.length) :
    satF w i (.atom p) = p w[i] := by
  simp [satF, List.getElem?_eq_getElem h]

theorem satF_atom_ge {w : List α} {i : Nat} {p : α → Bool} (h : w.length ≤ i) :
    satF w i (.atom p) = false := by
  simp [satF, List.getElem?_eq_none h]

theorem satF_until_iff {w : List α} {i : Nat} {φ ψ : LTL α} :
    satF w i (.until φ ψ) = true ↔
      ∃ k, i ≤ k ∧ k < w.length ∧ satF w k ψ = true ∧
        ∀ j, i ≤ j → j < k → satF w j φ = true := by
  simp only [satF]
  rw [untilF_iff]
  constructor
  · rintro ⟨k, h1, h2, h3, h4⟩; exact ⟨k, h1, by omega, h3, h4⟩
  · rintro ⟨k, h1, h2, h3, h4⟩; exact ⟨k, h1, by omega, h3, h4⟩

theorem satF_eventually_iff {w : List α} {i : Nat} {φ : LTL α} :
    satF w i (.eventually φ) = true ↔ ∃ k, i ≤ k ∧ k < w.length ∧ satF w k φ = true := by
  show satF w i (.until .tt φ) = true ↔ _
  rw [satF_until_iff]
  constructor
  · rintro ⟨k, h1, h2, h3, _⟩; exact ⟨k, h1, h2, h3⟩
  · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, h1, h2, h3, fun _ _ _ => rfl⟩

theorem satF_always_iff {w : List α} {i : Nat} {φ : LTL α} :
    satF w i (.always φ) = true ↔ ∀ k, i ≤ k → k < w.length → satF w k φ = true := by
  show (!satF w i (.eventually (.not φ))) = true ↔ _
  rw [Bool.not_eq_true', ← Bool.not_eq_true, satF_eventually_iff]
  constructor
  · intro h k h1 h2
    cases hk : satF w k φ
    · exact absurd ⟨k, h1, h2, by simp [satF, hk]⟩ h
    · rfl
  · rintro h ⟨k, h1, h2, hk⟩
    simp [satF, h k h1 h2] at hk

theorem satF_wnext_iff {w : List α} {i : Nat} {φ : LTL α} :
    satF w i (.wnext φ) = true ↔ (i + 1 < w.length → satF w (i + 1) φ = true) := by
  show (!(decide (i + 1 < w.length) && !satF w (i + 1) φ)) = true ↔ _
  by_cases h : i + 1 < w.length <;> simp [h]

theorem satF_always_atom {w : List α} {p : α → Bool} :
    satF w 0 (.always (.atom p)) = w.all p := by
  apply Bool.eq_iff_iff.2
  rw [satF_always_iff, List.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := h k (Nat.zero_le _) hk
    rwa [satF_atom_lt hk] at this
  · intro h k _ hk
    rw [satF_atom_lt hk]
    exact h _ (List.getElem_mem hk)

/-! ## Safety and co-safety fragments -/

/-- Syntactic safety fragment: no `until`, `eventually` or strong `next`.
Derived forms are listed before `and`/`or` so `constructor` picks them. -/
inductive Safe : LTL α → Prop
  | tt : Safe .tt
  | atom (p : α → Bool) : Safe (.atom p)
  | natom (p : α → Bool) : Safe (.not (.atom p))
  | wnext {φ : LTL α} : Safe φ → Safe (.wnext φ)
  | always {φ : LTL α} : Safe φ → Safe (.always φ)
  | wuntil {φ ψ : LTL α} : Safe φ → Safe ψ → Safe (.wuntil φ ψ)
  | and {φ ψ : LTL α} : Safe φ → Safe ψ → Safe (.and φ ψ)
  | or {φ ψ : LTL α} : Safe φ → Safe ψ → Safe (.or φ ψ)

/-- Syntactic co-safety fragment: no `always`, `wnext` or `wuntil`. -/
inductive CoSafe : LTL α → Prop
  | tt : CoSafe .tt
  | atom (p : α → Bool) : CoSafe (.atom p)
  | natom (p : α → Bool) : CoSafe (.not (.atom p))
  | eventually {φ : LTL α} : CoSafe φ → CoSafe (.eventually φ)
  | next {φ : LTL α} : CoSafe φ → CoSafe (.next φ)
  | until {φ ψ : LTL α} : CoSafe φ → CoSafe ψ → CoSafe (.until φ ψ)
  | and {φ ψ : LTL α} : CoSafe φ → CoSafe ψ → CoSafe (.and φ ψ)
  | or {φ ψ : LTL α} : CoSafe φ → CoSafe ψ → CoSafe (.or φ ψ)

theorem satF_prefix_atom {w : Nat → α} {n i : Nat} {p : α → Bool} (h : i < n) :
    satF (prefixOf w n) i (.atom p) = p (w i) := by
  simp [satF, prefix_get w h]

theorem safe_prefix_at {φ : LTL α} (hφ : Safe φ) {w : Nat → α} {i n : Nat}
    (h : sat w i φ) (hn : i < n) : satF (prefixOf w n) i φ = true := by
  induction hφ generalizing i with
  | tt => rfl
  | atom p => rw [satF_prefix_atom hn]; exact h
  | natom p =>
    show (!satF (prefixOf w n) i (.atom p)) = true
    rw [satF_prefix_atom hn]
    cases hp : p (w i)
    · rfl
    · exact absurd hp h
  | wnext _ ih =>
    rw [satF_wnext_iff]
    intro h1
    exact ih (sat_wnext_iff.1 h) (by simpa using h1)
  | always _ ih =>
    rw [satF_always_iff]
    intro k hk hkn
    exact ih (sat_always_iff.1 h k hk) (by simpa using hkn)
  | wuntil _ _ ihφ ihψ =>
    show (satF (prefixOf w n) i (.until _ _) || satF (prefixOf w n) i (.always _)) = true
    rw [Bool.or_eq_true, satF_until_iff, satF_always_iff]
    rcases h with ⟨k, hk, hψ, hφ⟩ | h
    · by_cases hkn : k < n
      · exact Or.inl ⟨k, hk, by simpa using hkn, ihψ hψ hkn,
          fun j h1 h2 => ihφ (hφ j h1 h2) (by omega)⟩
      · exact Or.inr fun j h1 h2 => ihφ (hφ j h1 (by simp at h2; omega)) (by simpa using h2)
    · exact Or.inr fun j h1 h2 => ihφ (sat_always_iff.1 h j h1) (by simpa using h2)
  | and _ _ ih1 ih2 =>
    show (satF _ _ _ && satF _ _ _) = true
    rw [Bool.and_eq_true]
    exact ⟨ih1 h.1 hn, ih2 h.2 hn⟩
  | or _ _ ih1 ih2 =>
    show (satF _ _ _ || satF _ _ _) = true
    rw [Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl (ih1 h hn)
    · exact Or.inr (ih2 h hn)

/-- Monitor soundness, positive form: a safe formula true on an infinite
trace is true on each of its non-empty finite prefixes. -/
theorem safe_prefix {φ : LTL α} (hφ : Safe φ) {w : Nat → α} {n : Nat}
    (h : sat w 0 φ) (hn : 1 ≤ n) : satF (prefixOf w n) 0 φ = true :=
  safe_prefix_at hφ h (by omega)

theorem cosafe_prefix_at {φ : LTL α} (hφ : CoSafe φ) {w : Nat → α} {i n : Nat}
    (hn : i < n) (h : satF (prefixOf w n) i φ = true) : sat w i φ := by
  induction hφ generalizing i with
  | tt => trivial
  | atom p => rw [satF_prefix_atom hn] at h; exact h
  | natom p =>
    have h' : (!satF (prefixOf w n) i (.atom p)) = true := h
    rw [satF_prefix_atom hn] at h'
    intro hp
    have hp' : p (w i) = true := hp
    simp [hp'] at h'
  | eventually _ ih =>
    rw [satF_eventually_iff] at h
    obtain ⟨k, hk, hkn, hφ⟩ := h
    exact sat_eventually_iff.2 ⟨k, hk, ih (by simpa using hkn) hφ⟩
  | next _ ih =>
    have h' : (decide (i + 1 < (prefixOf w n).length) && satF (prefixOf w n) (i + 1) _) = true := h
    rw [Bool.and_eq_true, decide_eq_true_iff] at h'
    exact ih (by simpa using h'.1) h'.2
  | «until» _ _ ihφ ihψ =>
    rw [satF_until_iff] at h
    obtain ⟨k, hk, hkn, hψ, hφ⟩ := h
    have hkn' : k < n := by simpa using hkn
    exact ⟨k, hk, ihψ hkn' hψ, fun j h1 h2 => ihφ (by omega) (hφ j h1 h2)⟩
  | and _ _ ih1 ih2 =>
    have h' : (satF _ _ _ && satF _ _ _) = true := h
    rw [Bool.and_eq_true] at h'
    exact ⟨ih1 hn h'.1, ih2 hn h'.2⟩
  | or _ _ ih1 ih2 =>
    have h' : (satF _ _ _ || satF _ _ _) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact Or.inl (ih1 hn h')
    · exact Or.inr (ih2 hn h')

/-- A co-safe formula witnessed on a non-empty finite prefix holds on the
infinite trace. -/
theorem cosafe_prefix {φ : LTL α} (hφ : CoSafe φ) {w : Nat → α} {n : Nat}
    (hn : 1 ≤ n) (h : satF (prefixOf w n) 0 φ = true) : sat w 0 φ :=
  cosafe_prefix_at hφ (by omega) h

end Architecton.Temporal
