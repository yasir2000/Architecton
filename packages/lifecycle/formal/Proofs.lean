import StateMachine
/-!
Machine-checkable assurance obligations for Architecton's RUP extension.
These are about lifecycle *states* and assumed trusted evidence, NOT about
whether a particular BRD, UML view, Rust binary, or deployed workload is correct.
No `axiom`, `admit`, or `sorry` is used in these proofs.
-/
namespace Architecton.Lifecycle

/-- LC-001: A successful phase promotion must satisfy the gate. -/
theorem successful_promotion_requires_gate (s : ProcessState)
    (h : (step s .promote).2 = .accepted) : Gate s := by
  cases hn : nextPhase s.phase with
  | none => simp [step, hn] at h
  | some target =>
      cases hg : gateSatisfied s with
      | true =>
          change gateSatisfied s = true
          exact hg
      | false => simp [step, hn, hg] at h

/-- LC-002: A successful promotion can only advance to its direct successor. -/
theorem successful_promotion_has_direct_successor (s : ProcessState)
    (h : (step s .promote).2 = .accepted) :
    ∃ target, nextPhase s.phase = some target ∧
      (step s .promote).1.phase = target := by
  cases hn : nextPhase s.phase with
  | none => simp [step, hn] at h
  | some target =>
      cases hg : gateSatisfied s with
      | true =>
          -- Depending on the Lean version, `cases` may already have rewritten
          -- the goal to `some target = some target`.
          refine ⟨target, by first | rfl | exact hn, ?_⟩
          simp [step, hn, hg]
      | false => simp [step, hn, hg] at h

/-- LC-003: Rejected promotions do not mutate any process state. -/
theorem blocked_promotion_preserves_state (s : ProcessState)
    (h : (step s .promote).2 = .blocked) :
    (step s .promote).1 = s := by
  cases hn : nextPhase s.phase with
  | none => simp [step, hn]
  | some target =>
      cases hg : gateSatisfied s with
      | true => simp [step, hn, hg] at h
      | false => simp [step, hn, hg]

/-- LC-004: An iteration preserves the baseline and already checked evidence. -/
theorem iteration_preserves_phase (s : ProcessState) :
    (step s .iterate).1.phase = s.phase := rfl

theorem iteration_preserves_evidence (s : ProcessState) :
    (step s .iterate).1.verified = s.verified := rfl

/-- LC-005: Revisions invalidate current evidence and return to Inception. -/
theorem revision_invalidates_evidence (s : ProcessState) :
    (step s .reviseRequirements).1.verified = [] := rfl

theorem revision_restarts_inception (s : ProcessState) :
    (step s .reviseRequirements).1.phase = .inception := rfl

theorem revision_archives_old_evidence (s : ProcessState) :
    (step s .reviseRequirements).1.archive =
      (s.revision, s.verified) :: s.archive := rfl

/-- A newly revised baseline must regain requirements and traceability review. -/
theorem revision_has_no_initial_gate (s : ProcessState) :
    ¬ Gate (step s .reviseRequirements).1 := by
  simp [step, Gate, gateSatisfied]

/-- LC-006: The construction→transition gate explicitly demands proof,
conformance, and build evidence, when that promotion is accepted. -/
theorem construction_release_requires_evidence (s : ProcessState)
    (hp : s.phase = .construction)
    (ha : (step s .promote).2 = .accepted) :
    s.verified.contains Evidence.proofChecked = true ∧
    s.verified.contains Evidence.conformancePassed = true ∧
    s.verified.contains Evidence.artifactBuilt = true := by
  have hg : Gate s := successful_promotion_requires_gate s ha
  cases h1 : s.verified.contains Evidence.proofChecked <;>
    cases h2 : s.verified.contains Evidence.conformancePassed <;>
    cases h3 : s.verified.contains Evidence.artifactBuilt <;>
    simp_all [Gate, gateSatisfied, hp]

/-- LC-007: Transition is terminal until requirements revision; no second
successful promotion or skip is possible. -/
theorem transition_not_promotable (s : ProcessState)
    (h : s.phase = .transition) :
    step s .promote = (s, .blocked) := by
  simp [step, nextPhase, h]

/-- LC-008: All RUP workflows remain enabled in every phase. -/
theorem workflows_are_cross_cutting (s : ProcessState) (w : Workflow) :
    workflowEnabled s w = true := rfl

end Architecton.Lifecycle
