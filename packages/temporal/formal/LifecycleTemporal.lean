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

/-! ## Liveness under fairness: L6

L6 needs three assumptions about the environment: requirements eventually
stop changing, every piece of gate evidence keeps being recorded, and
promotion keeps being attempted. `L6_needs_*` show that none can be dropped. -/

/-- Position of a phase in the RUP order. -/
def rank : Phase → Nat
  | .inception => 0
  | .elaboration => 1
  | .construction => 2
  | .transition => 3

theorem nextPhase_rank {p t : Phase} (h : nextPhase p = some t) : rank t = rank p + 1 := by
  cases p <;> simp [nextPhase] at h <;> subst h <;> rfl

def atTransition (r : LRec) : Bool := decide (r.post.phase = .transition)

/-- One step without a requirements revision never moves the phase back and
never loses evidence. -/
theorem step_mono (s : ProcessState) (c : Command) (hc : c ≠ .reviseRequirements) :
    rank s.phase ≤ rank (step s c).1.phase ∧ ∀ e ∈ s.verified, e ∈ (step s c).1.verified := by
  cases c with
  | recordValidated e => exact ⟨Nat.le_refl _, fun x hx => List.mem_cons_of_mem _ hx⟩
  | iterate => exact ⟨Nat.le_refl _, fun _ hx => hx⟩
  | reviseRequirements => exact absurd rfl hc
  | promote =>
    cases hn : nextPhase s.phase with
    | none => simp [step, hn]
    | some t =>
      cases hg : gateSatisfied s
      · simp [step, hn, hg]
      · simp [step, hn, hg, nextPhase_rank hn]

/-- A promotion whose gate holds advances exactly one phase. -/
theorem promote_advances (s : ProcessState) (hg : gateSatisfied s = true)
    (ht : s.phase ≠ .transition) : rank (step s .promote).1.phase = rank s.phase + 1 := by
  cases hn : nextPhase s.phase with
  | none => cases h : s.phase <;> simp_all [nextPhase]
  | some t => simp [step, hn, hg, nextPhase_rank hn]

/-- With all gate evidence recorded, every gate before `transition` holds. -/
theorem all_evidence_gate (s : ProcessState) (h : ∀ e ∈ gateEvidence, e ∈ s.verified)
    (ht : s.phase ≠ .transition) : gateSatisfied s = true := by
  rcases s with ⟨ph, it, rev, ver, arch⟩
  cases ph <;> simp_all [gateSatisfied, gateEvidence]

section L6proof

variable (u : Nat → Command)

theorem S_succ (n : Nat) :
    statesFrom lifecycle initial u (n + 1) = (step (statesFrom lifecycle initial u n) (u n)).1 := rfl

/-- After the last revision, the phase rank and the evidence only grow. -/
theorem mono_after (T : Nat) (hT : ∀ n ≥ T, u n ≠ .reviseRequirements) (n : Nat) (hn : T ≤ n) :
    ∀ k, rank (statesFrom lifecycle initial u n).phase ≤ rank (statesFrom lifecycle initial u (n + k)).phase ∧
      ∀ e ∈ (statesFrom lifecycle initial u n).verified, e ∈ (statesFrom lifecycle initial u (n + k)).verified := by
  intro k
  induction k with
  | zero => exact ⟨Nat.le_refl _, fun _ h => h⟩
  | succ k ih =>
    have hs := step_mono (statesFrom lifecycle initial u (n + k)) (u (n + k)) (hT _ (by omega))
    rw [← Nat.add_assoc, S_succ]
    exact ⟨Nat.le_trans ih.1 hs.1, fun e he => hs.2 e (ih.2 e he)⟩

theorem mono_le (T : Nat) (hT : ∀ n ≥ T, u n ≠ .reviseRequirements) {n m : Nat}
    (hn : T ≤ n) (hm : n ≤ m) :
    rank (statesFrom lifecycle initial u n).phase ≤ rank (statesFrom lifecycle initial u m).phase ∧
      ∀ e ∈ (statesFrom lifecycle initial u n).verified, e ∈ (statesFrom lifecycle initial u m).verified := by
  have := mono_after u T hT n hn (m - n)
  rwa [Nat.add_sub_cancel' hm] at this

/-- Eventually, after the last revision, every gate's evidence is recorded. -/
theorem evidence_collected (T : Nat) (hT : ∀ n ≥ T, u n ≠ .reviseRequirements)
    (hrec : ∀ e ∈ gateEvidence, ∀ n, ∃ m ≥ n, u m = .recordValidated e) :
    ∀ L : List Evidence, (∀ e ∈ L, e ∈ gateEvidence) →
      ∃ M ≥ T, ∀ e ∈ L, e ∈ (statesFrom lifecycle initial u M).verified := by
  intro L
  induction L with
  | nil => exact fun _ => ⟨T, Nat.le_refl _, fun _ h => absurd h List.not_mem_nil⟩
  | cons e L ih =>
    intro hL
    obtain ⟨M, hM, hall⟩ := ih fun x hx => hL x (List.mem_cons_of_mem _ hx)
    obtain ⟨m, hm, hu⟩ := hrec e (hL e List.mem_cons_self) M
    refine ⟨m + 1, by omega, fun x hx => ?_⟩
    have hrecd : e ∈ (statesFrom lifecycle initial u (m + 1)).verified := by
      rw [S_succ, hu]; exact List.mem_cons_self
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hrecd
    · exact (mono_le u T hT (by omega) (by omega : M ≤ m + 1)).2 x (hall x hx)

end L6proof

/-- L6: liveness under fairness. -/
theorem L6 (u : Nat → Command) (hrev : ∃ T, ∀ n ≥ T, u n ≠ .reviseRequirements)
    (hrec : ∀ e ∈ gateEvidence, ∀ n, ∃ m ≥ n, u m = .recordValidated e)
    (hpro : ∀ n, ∃ m ≥ n, u m = .promote) :
    sat (run lifecycle u) 0 (.eventually (.atom atTransition)) := by
  obtain ⟨T, hT⟩ := hrev
  obtain ⟨M, hMT, hM⟩ := evidence_collected u T hT hrec gateEvidence (fun _ h => h)
  have hev : ∀ n ≥ M, ∀ e ∈ gateEvidence, e ∈ (statesFrom lifecycle initial u n).verified :=
    fun n hn e he => (mono_le u T hT hMT hn).2 e (hM e he)
  -- from M on, each promotion attempt advances a phase until transition
  have climb : ∀ d, d ≤ 3 → ∃ n ≥ M, d ≤ rank (statesFrom lifecycle initial u n).phase := by
    intro d
    induction d with
    | zero => exact fun _ => ⟨M, Nat.le_refl _, Nat.zero_le _⟩
    | succ d ih =>
      intro hd
      obtain ⟨n, hn, hr⟩ := ih (by omega)
      by_cases hgt : d + 1 ≤ rank (statesFrom lifecycle initial u n).phase
      · exact ⟨n, hn, hgt⟩
      obtain ⟨m, hm, hp⟩ := hpro n
      have hmono := (mono_le u T hT (by omega) hm).1
      by_cases hgt' : d + 1 ≤ rank (statesFrom lifecycle initial u m).phase
      · exact ⟨m, by omega, hgt'⟩
      have hnt : (statesFrom lifecycle initial u m).phase ≠ .transition := by
        intro h; rw [h] at hgt'; simp [rank] at hgt'; omega
      have hadv := promote_advances _ (all_evidence_gate _ (hev m (by omega)) hnt) hnt
      refine ⟨m + 1, by omega, ?_⟩
      rw [S_succ, hp, hadv]
      omega
  obtain ⟨n, _, hn⟩ := climb 3 (Nat.le_refl _)
  have htr : (statesFrom lifecycle initial u n).phase = .transition := by
    revert hn; cases (statesFrom lifecycle initial u n).phase <;> simp [rank]
  cases n with
  | zero => simp [statesFrom, initial] at htr
  | succ j =>
    exact sat_eventually_iff.2 ⟨j, Nat.zero_le _, by
      show decide ((statesFrom lifecycle initial u (j + 1)).phase = .transition) = true
      simp [htr]⟩

/-- L6's assumptions as an LTL formula over the record trace. -/
def l6Assumptions : LTL LRec :=
  .and (.eventually (.always (.atom fun r => !decide (r.input = .reviseRequirements))))
    (.and (LTL.all (gateEvidence.map fun e => infOften (.atom fun r => decide (r.input = .recordValidated e))))
      (infOften (.atom fun r => decide (r.input = .promote))))

/-- L6 in pure LTL form: `assumptions → ◇ transition` holds on every run. -/
theorem L6_ltl (u : Nat → Command) :
    sat (run lifecycle u) 0 (.imp l6Assumptions (.eventually (.atom atTransition))) := by
  rw [sat_imp_iff]
  rintro ⟨h1, h2, h3⟩
  obtain ⟨T, hT⟩ := sat_eventually_always_iff.1 h1
  apply L6 u ⟨T, fun n hn hc => by
    have := hT n hn
    simp [sat, run, runFrom, recAt, hc] at this⟩
  · intro e he n
    have := sat_all_iff.1 h2 _ (List.mem_map.2 ⟨e, he, rfl⟩)
    obtain ⟨m, hm, hp⟩ := sat_infOften_atom_iff.1 this n
    exact ⟨m, hm, of_decide_eq_true hp⟩
  · intro n
    obtain ⟨m, hm, hp⟩ := sat_infOften_atom_iff.1 h3 n
    exact ⟨m, hm, of_decide_eq_true hp⟩

/-! ### Necessity of each L6 assumption -/

theorem gateEvidence_index : ∀ e ∈ gateEvidence, ∃ k < 7, gateEvidence.getD k .artifactBuilt = e := by
  intro e he
  simp only [gateEvidence, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩

/-- Fair stream, period 8: record all seven items, then promote. -/
def uFair (n : Nat) : Command :=
  if n % 8 < 7 then .recordValidated (gateEvidence.getD (n % 8) .artifactBuilt) else .promote

theorem uFair_assumptions :
    (∃ T, ∀ n ≥ T, uFair n ≠ .reviseRequirements) ∧
    (∀ e ∈ gateEvidence, ∀ n, ∃ m ≥ n, uFair m = .recordValidated e) ∧
    (∀ n, ∃ m ≥ n, uFair m = .promote) := by
  refine ⟨⟨0, fun n _ => ?_⟩, fun e he n => ?_, fun n => ⟨8 * n + 7, by omega, ?_⟩⟩
  · unfold uFair; split <;> simp
  · obtain ⟨k, hk, rfl⟩ := gateEvidence_index e he
    refine ⟨8 * n + k, by omega, ?_⟩
    have : (8 * n + k) % 8 = k := by omega
    simp [uFair, this, hk]
  · have : (8 * n + 7) % 8 = 7 := by omega
    simp [uFair, this]

/-- Never promote: period 7, the seven records. -/
def uNoPromote (n : Nat) : Command := .recordValidated (gateEvidence.getD (n % 7) .artifactBuilt)

theorem uNoPromote_other_assumptions :
    (∃ T, ∀ n ≥ T, uNoPromote n ≠ .reviseRequirements) ∧
    (∀ e ∈ gateEvidence, ∀ n, ∃ m ≥ n, uNoPromote m = .recordValidated e) := by
  refine ⟨⟨0, fun n _ => by simp [uNoPromote]⟩, fun e he n => ?_⟩
  obtain ⟨k, hk, rfl⟩ := gateEvidence_index e he
  refine ⟨7 * n + k, by omega, ?_⟩
  have : (7 * n + k) % 7 = k := by omega
  simp [uNoPromote, this]

/-- Dropping `□◇ promote`: the run stays in inception. -/
theorem L6_needs_promote : ∀ n, (statesFrom lifecycle initial uNoPromote n).phase ≠ .transition := by
  intro n
  have := invariant_rule (sys := lifecycle) (s := initial) (u := uNoPromote)
    (fun s => decide (s.phase = .inception)) (fun c => decide (c ≠ .promote)) rfl
    (fun s c hc hs => by cases c <;> simp_all [lifecycle, step])
    (fun n => by simp [uNoPromote]) n
  simp at this; simp [this]

/-- Never record `artifactBuilt`: period 7, the first six records then promote. -/
def uNoArtifact (n : Nat) : Command :=
  if n % 7 < 6 then .recordValidated (gateEvidence.getD (n % 7) .artifactBuilt) else .promote

theorem uNoArtifact_other_assumptions :
    (∃ T, ∀ n ≥ T, uNoArtifact n ≠ .reviseRequirements) ∧ (∀ n, ∃ m ≥ n, uNoArtifact m = .promote) := by
  refine ⟨⟨0, fun n _ => ?_⟩, fun n => ⟨7 * n + 6, by omega, ?_⟩⟩
  · unfold uNoArtifact; split <;> simp
  · have : (7 * n + 6) % 7 = 6 := by omega
    simp [uNoArtifact, this]

theorem uNoArtifact_never_records : ∀ n, uNoArtifact n ≠ .recordValidated .artifactBuilt := by
  intro n
  have hk : ∀ k, k < 6 → gateEvidence.getD k .artifactBuilt ≠ .artifactBuilt := by decide
  unfold uNoArtifact
  split
  · next h => simpa using hk _ h
  · simp

/-- Dropping the evidence assumption: without `artifactBuilt` the
construction gate never holds, so `transition` is never reached. -/
theorem L6_needs_evidence : ∀ n, (statesFrom lifecycle initial uNoArtifact n).phase ≠ .transition := by
  intro n
  have := invariant_rule (sys := lifecycle) (s := initial) (u := uNoArtifact)
    (fun s => !s.verified.contains .artifactBuilt && decide (s.phase ≠ .transition))
    (fun c => decide (c ≠ .recordValidated .artifactBuilt) && decide (c ≠ .reviseRequirements)) rfl
    (fun s c hc hs => by
      rcases s with ⟨ph, it, rev, ver, arch⟩
      cases c with
      | promote => cases ph <;> simp_all [lifecycle, step, nextPhase, gateSatisfied] <;> split <;> simp_all
      | _ => simp_all [lifecycle, step] <;> exact fun h => hc h.symm)
    (fun n => by
      have h1 := uNoArtifact_never_records n
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨h1, ?_⟩
      unfold uNoArtifact; split <;> simp) n
  simp at this; exact this.2

/-- Revise every period: period 9, revise, the seven records, promote. -/
def uRevise (n : Nat) : Command :=
  if n % 9 = 0 then .reviseRequirements
  else if n % 9 = 8 then .promote
  else .recordValidated (gateEvidence.getD (n % 9 - 1) .artifactBuilt)

theorem uRevise_other_assumptions :
    (∀ e ∈ gateEvidence, ∀ n, ∃ m ≥ n, uRevise m = .recordValidated e) ∧
    (∀ n, ∃ m ≥ n, uRevise m = .promote) := by
  refine ⟨fun e he n => ?_, fun n => ⟨9 * n + 8, by omega, ?_⟩⟩
  · obtain ⟨k, hk, rfl⟩ := gateEvidence_index e he
    refine ⟨9 * n + k + 1, by omega, ?_⟩
    have : (9 * n + k + 1) % 9 = k + 1 := by omega
    simp [uRevise, this, show k + 1 ≠ 8 by omega]
  · have : (9 * n + 8) % 9 = 8 := by omega
    simp [uRevise, this]

/-- Dropping `◇□ ¬revise`: revising once per period keeps the run in
inception or elaboration forever. -/
theorem L6_needs_no_revise : ∀ n, (statesFrom lifecycle initial uRevise n).phase ≠ .transition := by
  have inv : ∀ n, (n % 9 = 0 → rank (statesFrom lifecycle initial uRevise n).phase ≤ 1) ∧
      (n % 9 ≠ 0 → (statesFrom lifecycle initial uRevise n).phase = .inception) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => by simp [statesFrom, initial, rank], fun h => absurd rfl h⟩
    | succ n ih =>
      have hs := S_succ uRevise n
      by_cases h0 : n % 9 = 0
      · have hu : uRevise n = .reviseRequirements := by simp [uRevise, h0]
        have hph : (statesFrom lifecycle initial uRevise (n + 1)).phase = .inception := by
          rw [hs, hu]; rfl
        exact ⟨fun _ => by rw [hph]; simp [rank], fun _ => hph⟩
      by_cases h8 : n % 9 = 8
      · have hu : uRevise n = .promote := by simp [uRevise, h8]
        have hin := ih.2 h0
        have hph : rank (statesFrom lifecycle initial uRevise (n + 1)).phase ≤ 1 := by
          rw [hs, hu]
          generalize statesFrom lifecycle initial uRevise n = s at hin ⊢
          rcases s with ⟨ph, it, rev, ver, arch⟩
          simp at hin; subst hin
          cases hg : gateSatisfied ⟨.inception, it, rev, ver, arch⟩ <;> simp_all [step, nextPhase, rank]
        exact ⟨fun _ => hph, fun h => absurd (by omega) h⟩
      · have hu : uRevise n = .recordValidated (gateEvidence.getD (n % 9 - 1) .artifactBuilt) := by
          simp [uRevise, h0, h8]
        have hph : (statesFrom lifecycle initial uRevise (n + 1)).phase = .inception := by
          rw [hs, hu]; exact ih.2 h0
        exact ⟨fun h => absurd h (by omega), fun _ => hph⟩
  intro n h
  by_cases h0 : n % 9 = 0
  · have := (inv n).1 h0
    rw [h] at this; simp [rank] at this
  · have := (inv n).2 h0
    rw [h] at this; cases this

end Architecton.Temporal
