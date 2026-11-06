/-!
Architecton evidence ledger: the validity rule and its revocation theorems.

An entry records one check run (inputs, command, result, signer) and the
entries it depends on. A verifier treats an entry as BLOCKED when it is
revoked, its signature fails, its result is not `pass`, or one of its inputs
changed since it ran. An entry is VALID when it is present, not blocked, and
every entry it depends on is valid.

Main result (`valid_blockMore_iff`): blocking any further set `S` of entries
(revoking them, or changing files they read) invalidates EXACTLY the valid
entries that depend, directly or transitively, on a member of `S`. Nothing
else loses validity. That set is the scope that must be re-verified, and
`scripts/ledger.py plan` computes it.

The theorem assumes `Unique`: an entry ID determines the entry. The Python
ledger guarantees this by content addressing (ID = SHA-256 of the entry).
No `sorry`, no `axiom`.
-/
namespace Architecton.Ledger

abbrev Id := String

structure Entry where
  id : Id
  deps : List Id

structure Ledger where
  entries : List Entry
  /-- revoked, bad signature, failed result, or stale inputs -/
  blocked : Id → Prop

/-- Content addressing: one ID, one entry. -/
def Unique (L : Ledger) : Prop :=
  ∀ e₁ ∈ L.entries, ∀ e₂ ∈ L.entries, e₁.id = e₂.id → e₁ = e₂

inductive Valid (L : Ledger) : Id → Prop
  | intro (e : Entry) : e ∈ L.entries → ¬ L.blocked e.id →
      (∀ d ∈ e.deps, Valid L d) → Valid L e.id

/-- `Reaches L a b`: `a` depends on `b`, directly or transitively (or `a = b`). -/
inductive Reaches (L : Ledger) : Id → Id → Prop
  | refl (a : Id) : Reaches L a a
  | step (e : Entry) {d b : Id} : e ∈ L.entries → d ∈ e.deps → Reaches L d b →
      Reaches L e.id b

/-- Block the extra set `S` too. -/
def Ledger.blockMore (L : Ledger) (S : Id → Prop) : Ledger :=
  { L with blocked := fun i => L.blocked i ∨ S i }

/-- A valid entry's dependencies are all valid. -/
theorem valid_deps {L : Ledger} (hu : Unique L) {e : Entry} (he : e ∈ L.entries)
    (hv : Valid L e.id) : ∀ d ∈ e.deps, Valid L d := by
  generalize hi : e.id = i at hv
  cases hv with
  | intro e' he' _ hdeps =>
      have : e' = e := hu e' he' e he hi.symm
      subst this
      exact hdeps

/-- Validity is transitive along dependencies. -/
theorem valid_reaches {L : Ledger} (hu : Unique L) {a b : Id} (hr : Reaches L a b)
    (hv : Valid L a) : Valid L b := by
  induction hr with
  | refl => exact hv
  | @step e d b he hd _ ih => exact ih (valid_deps hu he hv d hd)

/-- Nothing that depends on a blocked entry is valid. -/
theorem not_valid_of_reaches_blocked {L : Ledger} (hu : Unique L) {a b : Id}
    (hr : Reaches L a b) (hb : L.blocked b) : ¬ Valid L a := by
  intro hv
  cases valid_reaches hu hr hv with
  | intro e _ hnb _ => exact hnb hb

/-- Blocking more never makes anything newly valid. -/
theorem valid_of_valid_blockMore {L : Ledger} {S : Id → Prop} {i : Id}
    (hv : Valid (L.blockMore S) i) : Valid L i := by
  induction hv with
  | intro e he hnb _ ih =>
      exact Valid.intro e he (fun h => hnb (Or.inl h)) ih

/-- Entries that do not depend on anything in `S` keep their validity. -/
theorem valid_blockMore_of_independent {L : Ledger} {S : Id → Prop} {i : Id}
    (hv : Valid L i) (hind : ∀ b, S b → ¬ Reaches L i b) : Valid (L.blockMore S) i := by
  induction hv with
  | intro e he hnb hdeps ih =>
      refine Valid.intro e he ?_ ?_
      · rintro (h | h)
        · exact hnb h
        · exact hind e.id h (Reaches.refl _)
      · intro d hd
        exact ih d hd (fun b hb hr => hind b hb (Reaches.step e he hd hr))

/-- Dependency paths ignore `blocked`, so blocking more keeps them. -/
theorem reaches_blockMore {L : Ledger} {S : Id → Prop} {a b : Id}
    (hr : Reaches L a b) : Reaches (L.blockMore S) a b := by
  induction hr with
  | refl => exact Reaches.refl _
  | step e he hd _ ih => exact Reaches.step e he hd ih

/-- Entries still valid after blocking `S` do not depend on anything in `S`. -/
theorem independent_of_valid_blockMore {L : Ledger} (hu : Unique L) {S : Id → Prop}
    {i : Id} (hv : Valid (L.blockMore S) i) : ∀ b, S b → ¬ Reaches L i b := by
  intro b hb hr
  have hu' : Unique (L.blockMore S) := hu
  exact not_valid_of_reaches_blocked hu' (reaches_blockMore hr) (Or.inr hb) hv

/-- **Exact revocation scope.** After blocking `S`, an entry is valid iff it
was valid before and depends on nothing in `S`. -/
theorem valid_blockMore_iff {L : Ledger} (hu : Unique L) (S : Id → Prop) (i : Id) :
    Valid (L.blockMore S) i ↔ Valid L i ∧ ∀ b, S b → ¬ Reaches L i b :=
  ⟨fun hv => ⟨valid_of_valid_blockMore hv, independent_of_valid_blockMore hu hv⟩,
   fun ⟨hv, hind⟩ => valid_blockMore_of_independent hv hind⟩

/-- Revoking a single entry `r` invalidates exactly its dependents. -/
theorem revoke_scope {L : Ledger} (hu : Unique L) (r i : Id) :
    Valid (L.blockMore (· = r)) i ↔ Valid L i ∧ ¬ Reaches L i r := by
  rw [valid_blockMore_iff hu]
  constructor
  · rintro ⟨hv, h⟩; exact ⟨hv, h r rfl⟩
  · rintro ⟨hv, h⟩; exact ⟨hv, fun b hb => hb ▸ h⟩

end Architecton.Ledger
