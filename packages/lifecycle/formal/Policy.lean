/-! Auto-generated from requirements/policy.json (SHA-256 prefix 5bd4fdad25a5b213).
DO NOT EDIT: python3 scripts/generate_policy.py --write
The gate encodes reviewed policy conditions; it is not itself a proof
that an actual artifact was verified by a trusted system. -/
import ArchitectonLifecycle
namespace Architecton.Lifecycle

/-- Decidable phase-promotion gate under the reviewed policy. -/
def gateSatisfied (s : ProcessState) : Bool :=
  match s.phase with
  | .inception =>
      (s.verified.contains Evidence.requirementsReviewed && s.verified.contains Evidence.traceabilityReviewed)
  | .elaboration =>
      (s.verified.contains Evidence.designReviewed && s.verified.contains Evidence.formalSpecificationChecked)
  | .construction =>
      ((s.verified.contains Evidence.proofChecked && s.verified.contains Evidence.conformancePassed) && s.verified.contains Evidence.artifactBuilt)
  | .transition => false

/-- Proposition-level reading of the executable Boolean gate. -/
def Gate (s : ProcessState) : Prop := gateSatisfied s = true

end Architecton.Lifecycle
