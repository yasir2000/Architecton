/-!
Architecton lifecycle domain: the process-state types of a proof-oriented
iterative/incremental engineering lifecycle. No business-specific axioms.

An attestation in `verified` means an *external trusted checker* has already
validated an artifact. Authentication, signatures and checking actual content
are outside this model, and this limitation is important.
-/
namespace Architecton.Lifecycle

inductive Phase where
  | inception | elaboration | construction | transition
  deriving DecidableEq, Repr

inductive Evidence where
  | requirementsReviewed
  | traceabilityReviewed
  | designReviewed
  | formalSpecificationChecked
  | proofChecked
  | conformancePassed
  | artifactBuilt
  | deploymentValidated
  deriving DecidableEq, Repr

/-- The familiar RUP activities overlap across ALL phases; formal verification
is an additional cross-cutting workflow, not a fifth phase. -/
inductive Workflow where
  | businessModeling | requirements | analysisDesign | implementation
  | test | deployment | configurationChange | projectManagement
  | environment | formalVerification
  deriving DecidableEq, Repr

/-- A phase-gated baseline. Prior revisions are archived, never silently reused. -/
structure ProcessState where
  phase : Phase
  iteration : Nat
  revision : Nat
  verified : List Evidence
  archive : List (Nat × List Evidence)
  deriving Repr, DecidableEq

inductive Command where
  | recordValidated (evidence : Evidence)
  | iterate
  | promote
  | reviseRequirements
  deriving DecidableEq, Repr

inductive Outcome where
  | accepted | blocked
  deriving DecidableEq, Repr

/-- The initial requirements baseline. -/
def initial : ProcessState :=
  { phase := .inception, iteration := 0, revision := 0,
    verified := [], archive := [] }

/-- Ordered phase successor: no skipping and no further phase after transition. -/
def nextPhase : Phase → Option Phase
  | .inception => some .elaboration
  | .elaboration => some .construction
  | .construction => some .transition
  | .transition => none

/-- Workflow execution is not restricted to a single phase. Effort allocation
by phase (RUP's curves) is intentionally not represented here. -/
def workflowEnabled (_s : ProcessState) (_w : Workflow) : Bool := true

end Architecton.Lifecycle
