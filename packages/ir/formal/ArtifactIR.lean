/-!
Architecton typed artifact IR, version 1: the Lean reference semantics.

The IR records goals, requirement statements, risks, typed state variables,
typed state transitions, invariants, artifacts and provenance anchors.

This file defines
* a small, closed, typed expression language for guards, effects and invariants;
* its type checker `typeOf` and its evaluator `eval`;
* `wellFormed`, a decidable check over a whole IR model;
* theorems: type soundness of the expression language, and that every guard,
  effect and invariant of a well-formed model evaluates to a value of the
  declared type in every state that conforms to the model's declarations.

Out of scope here: artifact hashes and anchor text are checked by
`scripts/irc.py`, not by Lean. Whether the IR faithfully captures the
natural-language requirements is a human review decision.
No `sorry`, no `axiom`.
-/
namespace Architecton.IR

/-! ## Types, values and expressions -/

inductive Ty where
  | bool | nat | natList
  deriving DecidableEq, Repr

inductive Val where
  | bool (b : Bool)
  | nat (n : Nat)
  | natList (l : List Nat)
  deriving DecidableEq, Repr

def Val.ty : Val → Ty
  | .bool _ => .bool
  | .nat _ => .nat
  | .natList _ => .natList

/-- Closed expression vocabulary. Fixed arities keep the type checker,
evaluator and proofs structural. -/
inductive Expr where
  | var (name : String)
  | param (name : String)
  | litBool (b : Bool)
  | litNat (n : Nat)
  | not (e : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | eqNat (a b : Expr)
  | contains (l x : Expr)
  | cons (x l : Expr)
  | nodup (l : Expr)
  deriving DecidableEq, Repr

/-- Typing context: declared names and types. -/
abbrev Ctx := List (String × Ty)
/-- Runtime environment: names and values. -/
abbrev Env := List (String × Val)

/-! ## Type checker -/

def typeOf (vars params : Ctx) : Expr → Option Ty
  | .var n => vars.lookup n
  | .param n => params.lookup n
  | .litBool _ => some .bool
  | .litNat _ => some .nat
  | .not e =>
      match typeOf vars params e with
      | some .bool => some .bool
      | _ => none
  | .and a b =>
      match typeOf vars params a, typeOf vars params b with
      | some .bool, some .bool => some .bool
      | _, _ => none
  | .or a b =>
      match typeOf vars params a, typeOf vars params b with
      | some .bool, some .bool => some .bool
      | _, _ => none
  | .eqNat a b =>
      match typeOf vars params a, typeOf vars params b with
      | some .nat, some .nat => some .bool
      | _, _ => none
  | .contains l x =>
      match typeOf vars params l, typeOf vars params x with
      | some .natList, some .nat => some .bool
      | _, _ => none
  | .cons x l =>
      match typeOf vars params x, typeOf vars params l with
      | some .nat, some .natList => some .natList
      | _, _ => none
  | .nodup l =>
      match typeOf vars params l with
      | some .natList => some .bool
      | _ => none

/-! ## Evaluator -/

/-- Boolean "no duplicates" test on a list of naturals. -/
def distinctNat : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinctNat xs

def eval (σ ρ : Env) : Expr → Option Val
  | .var n => σ.lookup n
  | .param n => ρ.lookup n
  | .litBool b => some (.bool b)
  | .litNat n => some (.nat n)
  | .not e =>
      match eval σ ρ e with
      | some (.bool b) => some (.bool !b)
      | _ => none
  | .and a b =>
      match eval σ ρ a, eval σ ρ b with
      | some (.bool x), some (.bool y) => some (.bool (x && y))
      | _, _ => none
  | .or a b =>
      match eval σ ρ a, eval σ ρ b with
      | some (.bool x), some (.bool y) => some (.bool (x || y))
      | _, _ => none
  | .eqNat a b =>
      match eval σ ρ a, eval σ ρ b with
      | some (.nat x), some (.nat y) => some (.bool (x == y))
      | _, _ => none
  | .contains l x =>
      match eval σ ρ l, eval σ ρ x with
      | some (.natList xs), some (.nat y) => some (.bool (xs.contains y))
      | _, _ => none
  | .cons x l =>
      match eval σ ρ x, eval σ ρ l with
      | some (.nat y), some (.natList xs) => some (.natList (y :: xs))
      | _, _ => none
  | .nodup l =>
      match eval σ ρ l with
      | some (.natList xs) => some (.bool (distinctNat xs))
      | _ => none

/-- An environment conforms to a context when every declared name is bound
to a value of its declared type. -/
def Conforms (Γ : Ctx) (σ : Env) : Prop :=
  ∀ n t, Γ.lookup n = some t → ∃ v, σ.lookup n = some v ∧ v.ty = t

/-! ## Type soundness -/

private theorem val_of_ty_bool {v : Val} (h : v.ty = .bool) : ∃ b, v = .bool b := by
  cases v <;> simp [Val.ty] at h ⊢

private theorem val_of_ty_nat {v : Val} (h : v.ty = .nat) : ∃ n, v = .nat n := by
  cases v <;> simp [Val.ty] at h ⊢

private theorem val_of_ty_natList {v : Val} (h : v.ty = .natList) : ∃ l, v = .natList l := by
  cases v <;> simp [Val.ty] at h ⊢

/-- Well-typed expressions never get stuck: in an environment that conforms to
the typing contexts, a well-typed expression evaluates to a value of its type. -/
theorem eval_sound {Γ Δ : Ctx} {σ ρ : Env} (hσ : Conforms Γ σ) (hρ : Conforms Δ ρ) :
    ∀ (e : Expr) (t : Ty), typeOf Γ Δ e = some t →
      ∃ v, eval σ ρ e = some v ∧ v.ty = t := by
  intro e
  induction e with
  | var n => intro t h; exact hσ n t h
  | param n => intro t h; exact hρ n t h
  | litBool b => intro t h; simp [typeOf] at h; subst h; exact ⟨.bool b, rfl, rfl⟩
  | litNat n => intro t h; simp [typeOf] at h; subst h; exact ⟨.nat n, rfl, rfl⟩
  | not e ih =>
      intro t h
      simp only [typeOf] at h
      split at h <;> simp at h
      subst h
      next he =>
        obtain ⟨v, hv, hvt⟩ := ih .bool he
        obtain ⟨b, rfl⟩ := val_of_ty_bool hvt
        exact ⟨.bool !b, by simp [eval, hv], rfl⟩
  | and a b iha ihb =>
      intro t h
      simp only [typeOf] at h
      split at h <;> simp at h
      subst h
      next ha hb =>
        obtain ⟨va, hva, hvat⟩ := iha .bool ha
        obtain ⟨vb, hvb, hvbt⟩ := ihb .bool hb
        obtain ⟨x, rfl⟩ := val_of_ty_bool hvat
        obtain ⟨y, rfl⟩ := val_of_ty_bool hvbt
        exact ⟨.bool (x && y), by simp [eval, hva, hvb], rfl⟩
  | or a b iha ihb =>
      intro t h
      simp only [typeOf] at h
      split at h <;> simp at h
      subst h
      next ha hb =>
        obtain ⟨va, hva, hvat⟩ := iha .bool ha
        obtain ⟨vb, hvb, hvbt⟩ := ihb .bool hb
        obtain ⟨x, rfl⟩ := val_of_ty_bool hvat
        obtain ⟨y, rfl⟩ := val_of_ty_bool hvbt
        exact ⟨.bool (x || y), by simp [eval, hva, hvb], rfl⟩
  | eqNat a b iha ihb =>
      intro t h
      simp only [typeOf] at h
      split at h <;> simp at h
      subst h
      next ha hb =>
        obtain ⟨va, hva, hvat⟩ := iha .nat ha
        obtain ⟨vb, hvb, hvbt⟩ := ihb .nat hb
        obtain ⟨x, rfl⟩ := val_of_ty_nat hvat
        obtain ⟨y, rfl⟩ := val_of_ty_nat hvbt
        exact ⟨.bool (x == y), by simp [eval, hva, hvb], rfl⟩
  | contains l x ihl ihx =>
      intro t h
      simp only [typeOf] at h
      split at h <;> simp at h
      subst h
      next hl hx =>
        obtain ⟨vl, hvl, hvlt⟩ := ihl .natList hl
        obtain ⟨vx, hvx, hvxt⟩ := ihx .nat hx
        obtain ⟨xs, rfl⟩ := val_of_ty_natList hvlt
        obtain ⟨y, rfl⟩ := val_of_ty_nat hvxt
        exact ⟨.bool (xs.contains y), by simp [eval, hvl, hvx], rfl⟩
  | cons x l ihx ihl =>
      intro t h
      simp only [typeOf] at h
      split at h <;> simp at h
      subst h
      next hx hl =>
        obtain ⟨vx, hvx, hvxt⟩ := ihx .nat hx
        obtain ⟨vl, hvl, hvlt⟩ := ihl .natList hl
        obtain ⟨y, rfl⟩ := val_of_ty_nat hvxt
        obtain ⟨xs, rfl⟩ := val_of_ty_natList hvlt
        exact ⟨.natList (y :: xs), by simp [eval, hvx, hvl], rfl⟩
  | nodup l ih =>
      intro t h
      simp only [typeOf] at h
      split at h <;> simp at h
      subst h
      next hl =>
        obtain ⟨v, hv, hvt⟩ := ih .natList hl
        obtain ⟨xs, rfl⟩ := val_of_ty_natList hvt
        exact ⟨.bool (distinctNat xs), by simp [eval, hv], rfl⟩

/-! ## IR model -/

inductive ReqKind where
  | business | system | nonfunctional
  deriving DecidableEq, Repr

inductive RiskStatus where
  | mitigated | accepted | open
  deriving DecidableEq, Repr

/-- What an anchored artifact is to the element: where it came from, or where
it is designed, proved, implemented or tested. -/
inductive AnchorRole where
  | source | design | proof | implementation | test
  deriving DecidableEq, Repr

/-- A provenance anchor: a named location inside a declared artifact. -/
structure Anchor where
  artifact : String
  anchor : String
  role : AnchorRole
  deriving DecidableEq, Repr

structure Artifact where
  id : String
  path : String
  sha256 : String
  deriving DecidableEq, Repr

structure Goal where
  id : String
  parent : Option String
  provenance : List Anchor
  deriving DecidableEq, Repr

structure Requirement where
  id : String
  kind : ReqKind
  goals : List String
  provenance : List Anchor
  deriving DecidableEq, Repr

structure Risk where
  id : String
  status : RiskStatus
  mitigatedBy : List String
  provenance : List Anchor
  deriving DecidableEq, Repr

structure Guard where
  requirement : String
  cond : Expr
  outcome : String
  deriving DecidableEq, Repr

structure Assign where
  var : String
  value : Expr
  deriving DecidableEq, Repr

/-- A typed state transition: ordered guards; if none fires, the `otherwise`
requirement applies and the effect runs. Guards never mutate state. -/
structure Transition where
  id : String
  params : Ctx
  guards : List Guard
  otherwiseRequirement : String
  otherwiseOutcome : String
  effect : List Assign
  deriving DecidableEq, Repr

/-- A state invariant. It may mention state variables only, not parameters. -/
structure Invariant where
  id : String
  requirement : String
  body : Expr
  deriving DecidableEq, Repr

structure Model where
  goals : List Goal
  requirements : List Requirement
  risks : List Risk
  stateVars : Ctx
  transitions : List Transition
  invariants : List Invariant
  artifacts : List Artifact
  deriving DecidableEq, Repr

/-! ## Well-formedness -/

def distinct : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

def Model.goalIds (m : Model) : List String := m.goals.map (·.id)
def Model.reqIds (m : Model) : List String := m.requirements.map (·.id)
def Model.artifactIds (m : Model) : List String := m.artifacts.map (·.id)

def anchorsOk (m : Model) (ps : List Anchor) : Bool :=
  ps.all (fun p => m.artifactIds.contains p.artifact)

def parentOf (m : Model) (g : String) : Option String :=
  (m.goals.find? (·.id == g)).bind (·.parent)

/-- Following parent links from `g` reaches a root within `fuel` steps. With
`fuel` equal to the number of goals, this rules out cycles. -/
def reachesRoot (m : Model) : Nat → String → Bool
  | 0, _ => false
  | fuel + 1, g =>
      match parentOf m g with
      | none => true
      | some p => m.goalIds.contains p && reachesRoot m fuel p

def goalOk (m : Model) (g : Goal) : Bool :=
  (match g.parent with
   | none => true
   | some p => m.goalIds.contains p) &&
  reachesRoot m m.goals.length g.id &&
  anchorsOk m g.provenance

def requirementOk (m : Model) (r : Requirement) : Bool :=
  !r.goals.isEmpty && r.goals.all m.goalIds.contains && anchorsOk m r.provenance

def riskOk (m : Model) (k : Risk) : Bool :=
  k.mitigatedBy.all m.reqIds.contains &&
  (match k.status with
   | .mitigated => !k.mitigatedBy.isEmpty
   | _ => true) &&
  anchorsOk m k.provenance

def guardOk (m : Model) (tr : Transition) (g : Guard) : Bool :=
  typeOf m.stateVars tr.params g.cond == some .bool && m.reqIds.contains g.requirement

def assignOk (m : Model) (tr : Transition) (a : Assign) : Bool :=
  match m.stateVars.lookup a.var with
  | none => false
  | some t => typeOf m.stateVars tr.params a.value == some t

def transitionOk (m : Model) (tr : Transition) : Bool :=
  distinct (tr.params.map (·.1)) &&
  tr.guards.all (guardOk m tr) &&
  distinct (tr.effect.map (·.var)) &&
  tr.effect.all (assignOk m tr) &&
  m.reqIds.contains tr.otherwiseRequirement

def invariantOk (m : Model) (i : Invariant) : Bool :=
  typeOf m.stateVars [] i.body == some .bool && m.reqIds.contains i.requirement

def wellFormed (m : Model) : Bool :=
  distinct (m.goalIds ++ m.reqIds ++ m.risks.map (·.id) ++
            m.transitions.map (·.id) ++ m.invariants.map (·.id) ++ m.artifactIds) &&
  distinct (m.stateVars.map (·.1)) &&
  m.goals.all (goalOk m) &&
  m.requirements.all (requirementOk m) &&
  m.risks.all (riskOk m) &&
  m.transitions.all (transitionOk m) &&
  m.invariants.all (invariantOk m)

/-! ## Consequences of well-formedness -/

/-- In a well-formed model, every guard of every transition evaluates to a
Boolean in every conforming state and parameter environment: guards never get
stuck and never produce a non-Boolean. -/
theorem wf_guard_evaluates {m : Model} (hwf : wellFormed m = true)
    {tr : Transition} (htr : tr ∈ m.transitions) {g : Guard} (hg : g ∈ tr.guards)
    {σ ρ : Env} (hσ : Conforms m.stateVars σ) (hρ : Conforms tr.params ρ) :
    ∃ b, eval σ ρ g.cond = some (.bool b) := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true] at hwf
  have htrOk := hwf.1.2 tr htr
  simp only [transitionOk, Bool.and_eq_true, List.all_eq_true] at htrOk
  have hgOk := htrOk.1.1.1.2 g hg
  simp only [guardOk, Bool.and_eq_true, beq_iff_eq] at hgOk
  obtain ⟨v, hv, hvt⟩ := eval_sound hσ hρ g.cond .bool hgOk.1
  obtain ⟨b, rfl⟩ := val_of_ty_bool hvt
  exact ⟨b, hv⟩

/-- In a well-formed model, every effect assignment computes a value whose type
matches the declared type of the variable it writes. -/
theorem wf_effect_type_preserving {m : Model} (hwf : wellFormed m = true)
    {tr : Transition} (htr : tr ∈ m.transitions) {a : Assign} (ha : a ∈ tr.effect)
    {σ ρ : Env} (hσ : Conforms m.stateVars σ) (hρ : Conforms tr.params ρ) :
    ∃ t v, m.stateVars.lookup a.var = some t ∧ eval σ ρ a.value = some v ∧ v.ty = t := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true] at hwf
  have htrOk := hwf.1.2 tr htr
  simp only [transitionOk, Bool.and_eq_true, List.all_eq_true] at htrOk
  have haOk := htrOk.1.2 a ha
  simp only [assignOk] at haOk
  split at haOk
  · contradiction
  · next t ht =>
      simp only [beq_iff_eq] at haOk
      obtain ⟨v, hv, hvt⟩ := eval_sound hσ hρ a.value t haOk
      exact ⟨t, v, ht, hv, hvt⟩

/-- In a well-formed model, every invariant is a Boolean-valued predicate on
conforming states; parameters cannot leak into it. -/
theorem wf_invariant_evaluates {m : Model} (hwf : wellFormed m = true)
    {i : Invariant} (hi : i ∈ m.invariants)
    {σ : Env} (hσ : Conforms m.stateVars σ) (ρ : Env) :
    ∃ b, eval σ ρ i.body = some (.bool b) := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true] at hwf
  have hiOk := hwf.2 i hi
  simp only [invariantOk, Bool.and_eq_true, beq_iff_eq] at hiOk
  have hρ : Conforms [] ρ := by intro n t h; simp at h
  obtain ⟨v, hv, hvt⟩ := eval_sound hσ hρ i.body .bool hiOk.1
  obtain ⟨b, rfl⟩ := val_of_ty_bool hvt
  exact ⟨b, hv⟩

/-- Every requirement in a well-formed model refines at least one declared goal. -/
theorem wf_requirement_traced {m : Model} (hwf : wellFormed m = true)
    {r : Requirement} (hr : r ∈ m.requirements) :
    ∃ g, g ∈ r.goals ∧ g ∈ m.goalIds := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true] at hwf
  have hrOk := hwf.1.1.1.2 r hr
  simp only [requirementOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at hrOk
  obtain ⟨⟨hne, hall⟩, _⟩ := hrOk
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨g, hg, by simpa using hall g hg⟩

end Architecton.IR
