import StateMachine
namespace Architecton.Lifecycle

/-- A fresh project cannot promote without verified requirements. -/
example : (step initial .promote).2 = .blocked := by decide

/-- Requirements + traceability evidence allow only Inception→Elaboration. -/
def reviewed : ProcessState :=
  (step (step initial (.recordValidated .requirementsReviewed)).1
        (.recordValidated .traceabilityReviewed)).1

example : (step reviewed .promote).1.phase = .elaboration := by decide

/-- The Elaboration gate is independent from the Inception gate. -/
example : (step (step reviewed .promote).1 .promote).2 = .blocked := by decide

/-- Revision erases current release evidence while retaining an archive. -/
example : (step reviewed .reviseRequirements).1.verified = [] := by decide
example : (step reviewed .reviseRequirements).1.revision = 1 := by decide
example : (step reviewed .reviseRequirements).1.archive.length = 1 := by decide

/-- Iterating is not the same as promoting or revising a baseline. -/
example : (step reviewed .iterate).1.phase = .inception := by decide
example : (step reviewed .iterate).1.iteration = 1 := by decide

end Architecton.Lifecycle
