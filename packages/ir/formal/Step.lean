import ArtifactIR

/-!
Operational semantics of IR transitions.

`step tr σ ρ` runs transition `tr` in state `σ` with parameters `ρ`:
guards are tried in order; the first that evaluates to `true` yields its
outcome and leaves the state unchanged. If none fires, every effect is
evaluated in the PRE-state (simultaneous assignment), the results are written,
and the `otherwise` outcome is returned. `none` means evaluation got stuck.

Theorems, for every well-formed model:
* `step_progress`: a transition never gets stuck on conforming inputs;
* `step_preserves_conforms`: the resulting state still conforms to the
  declared state types.
No `sorry`, no `axiom`.
-/
namespace Architecton.IR

/-- Overwrite `n` with `v` in place, or append it if it is absent. -/
def Env.set : Env → String → Val → Env
  | [], n, v => [(n, v)]
  | (m, w) :: rest, n, v =>
      if m = n then (n, v) :: rest else (m, w) :: Env.set rest n v

/-- Evaluate all effect right-hand sides in the same pre-state. -/
def evalEffect (σ ρ : Env) : List Assign → Option (List (String × Val))
  | [] => some []
  | a :: as =>
      match eval σ ρ a.value, evalEffect σ ρ as with
      | some v, some rest => some ((a.var, v) :: rest)
      | _, _ => none

def writeAll (σ : Env) : List (String × Val) → Env
  | [] => σ
  | (n, v) :: rest => writeAll (σ.set n v) rest

/-- `some (some o)`: a guard fired with outcome `o`; `some none`: no guard
fired; `none`: a guard got stuck. -/
def fireGuards (σ ρ : Env) : List Guard → Option (Option String)
  | [] => some none
  | g :: gs =>
      match eval σ ρ g.cond with
      | some (.bool true) => some (some g.outcome)
      | some (.bool false) => fireGuards σ ρ gs
      | _ => none

def step (tr : Transition) (σ ρ : Env) : Option (Env × String) :=
  match fireGuards σ ρ tr.guards with
  | none => none
  | some (some o) => some (σ, o)
  | some none =>
      match evalEffect σ ρ tr.effect with
      | none => none
      | some ws => some (writeAll σ ws, tr.otherwiseOutcome)

/-! ## Lemmas about environments -/

theorem lookup_set_same (σ : Env) (n : String) (v : Val) :
    (σ.set n v).lookup n = some v := by
  induction σ with
  | nil => simp [Env.set]
  | cons p rest ih =>
      obtain ⟨m, w⟩ := p
      by_cases h : m = n
      · simp [Env.set, h]
      · have hne : (n == m) = false := by simp; exact fun e => h e.symm
        simp [Env.set, h, List.lookup, hne, ih]

theorem lookup_set_other (σ : Env) {n k : String} (v : Val) (hk : k ≠ n) :
    (σ.set n v).lookup k = σ.lookup k := by
  induction σ with
  | nil =>
      have : (k == n) = false := by simp [hk]
      simp [Env.set, List.lookup, this]
  | cons p rest ih =>
      obtain ⟨m, w⟩ := p
      by_cases h : m = n
      · subst h
        have : (k == m) = false := by simp [hk]
        simp [Env.set, List.lookup, this]
      · simp only [Env.set, h, ite_false, List.lookup]
        split <;> simp_all

/-- Writing a value of the declared type keeps an environment conforming. -/
theorem conforms_set {Γ : Ctx} {σ : Env} (hσ : Conforms Γ σ) {n : String} {v : Val}
    (ht : Γ.lookup n = some v.ty) : Conforms Γ (σ.set n v) := by
  intro k t hk
  by_cases h : k = n
  · subst h
    rw [ht] at hk
    exact ⟨v, lookup_set_same σ k v, Option.some.inj hk⟩
  · rw [lookup_set_other σ v h]
    exact hσ k t hk

theorem conforms_writeAll {Γ : Ctx} :
    ∀ {σ : Env} (ws : List (String × Val)), Conforms Γ σ →
      (∀ p ∈ ws, Γ.lookup p.1 = some p.2.ty) → Conforms Γ (writeAll σ ws)
  | _, [], hσ, _ => hσ
  | _, (n, v) :: rest, hσ, hws => by
      simp only [writeAll]
      apply conforms_writeAll rest
      · exact conforms_set hσ (hws (n, v) (by simp))
      · intro p hp; exact hws p (by simp [hp])

/-! ## Progress and preservation -/

private theorem wf_transition {m : Model} (hwf : wellFormed m = true)
    {tr : Transition} (htr : tr ∈ m.transitions) : transitionOk m tr = true := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true] at hwf
  exact hwf.1.2 tr htr

theorem fireGuards_progress {m : Model} {tr : Transition} {σ ρ : Env}
    (hσ : Conforms m.stateVars σ) (hρ : Conforms tr.params ρ) :
    ∀ gs : List Guard, (∀ g ∈ gs, guardOk m tr g = true) →
      ∃ r, fireGuards σ ρ gs = some r
  | [], _ => ⟨none, rfl⟩
  | g :: gs, hok => by
      have hg := hok g (by simp)
      simp only [guardOk, Bool.and_eq_true, beq_iff_eq] at hg
      obtain ⟨v, hv, hvt⟩ := eval_sound hσ hρ g.cond .bool hg.1
      cases v with
      | bool b =>
          cases b with
          | true => exact ⟨some g.outcome, by simp [fireGuards, hv]⟩
          | false =>
              obtain ⟨r, hr⟩ := fireGuards_progress hσ hρ gs
                (fun g' hg' => hok g' (by simp [hg']))
              exact ⟨r, by simp [fireGuards, hv, hr]⟩
      | nat _ => simp [Val.ty] at hvt
      | natList _ => simp [Val.ty] at hvt

theorem evalEffect_ok {m : Model} {tr : Transition} {σ ρ : Env}
    (hσ : Conforms m.stateVars σ) (hρ : Conforms tr.params ρ) :
    ∀ as : List Assign, (∀ a ∈ as, assignOk m tr a = true) →
      ∃ ws, evalEffect σ ρ as = some ws ∧ ∀ p ∈ ws, m.stateVars.lookup p.1 = some p.2.ty
  | [], _ => ⟨[], rfl, by simp⟩
  | a :: as, hok => by
      have ha := hok a (by simp)
      simp only [assignOk] at ha
      split at ha
      · contradiction
      · next t ht =>
          simp only [beq_iff_eq] at ha
          obtain ⟨v, hv, hvt⟩ := eval_sound hσ hρ a.value t ha
          obtain ⟨ws, hws, hall⟩ := evalEffect_ok hσ hρ as
            (fun a' ha' => hok a' (by simp [ha']))
          refine ⟨(a.var, v) :: ws, by simp [evalEffect, hv, hws], ?_⟩
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · simp [ht, hvt]
          · exact hall p hp

/-- Progress: in a well-formed model, a transition run on a conforming state
and conforming parameters always produces a result. -/
theorem step_progress {m : Model} (hwf : wellFormed m = true)
    {tr : Transition} (htr : tr ∈ m.transitions) {σ ρ : Env}
    (hσ : Conforms m.stateVars σ) (hρ : Conforms tr.params ρ) :
    ∃ r, step tr σ ρ = some r := by
  have hok := wf_transition hwf htr
  simp only [transitionOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨r, hr⟩ := fireGuards_progress hσ hρ tr.guards hok.1.1.1.2
  obtain ⟨ws, hws, _⟩ := evalEffect_ok hσ hρ tr.effect hok.1.2
  cases r with
  | none => exact ⟨(writeAll σ ws, tr.otherwiseOutcome), by simp [step, hr, hws]⟩
  | some o => exact ⟨(σ, o), by simp [step, hr]⟩

/-- Preservation: in a well-formed model, the state a transition produces
still conforms to the declared state types. -/
theorem step_preserves_conforms {m : Model} (hwf : wellFormed m = true)
    {tr : Transition} (htr : tr ∈ m.transitions) {σ ρ σ' : Env} {o : String}
    (hσ : Conforms m.stateVars σ) (hρ : Conforms tr.params ρ)
    (hstep : step tr σ ρ = some (σ', o)) : Conforms m.stateVars σ' := by
  have hok := wf_transition hwf htr
  simp only [transitionOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨ws, hws, hall⟩ := evalEffect_ok hσ hρ tr.effect hok.1.2
  unfold step at hstep
  split at hstep
  · contradiction
  · simp at hstep; rw [← hstep.1]; exact hσ
  · simp only [hws, Option.some.injEq, Prod.mk.injEq] at hstep
    rw [← hstep.1]
    exact conforms_writeAll ws hσ hall

end Architecton.IR
