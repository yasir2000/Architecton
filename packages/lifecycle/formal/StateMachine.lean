import Policy
/-!
Transition semantics for a phase-gated baseline; `Gate` is *generated* from
requirements/policy.json and checked separately from hand-written proofs.
-/
namespace Architecton.Lifecycle

/-- Record a trusted validation result, continue an iteration, promote one
phase if the gate holds, or invalidate evidence on a requirements revision. -/
def step (s : ProcessState) (command : Command) : ProcessState × Outcome :=
  match command with
  | .recordValidated e =>
      ({ s with verified := e :: s.verified }, .accepted)
  | .iterate =>
      ({ s with iteration := s.iteration + 1 }, .accepted)
  | .reviseRequirements =>
      ({ s with phase := .inception, iteration := s.iteration + 1,
                  revision := s.revision + 1, verified := [],
                  archive := (s.revision, s.verified) :: s.archive }, .accepted)
  | .promote =>
      match nextPhase s.phase with
      | none => (s, .blocked)
      | some target =>
          if gateSatisfied s then ({ s with phase := target }, .accepted)
          else (s, .blocked)

end Architecton.Lifecycle
