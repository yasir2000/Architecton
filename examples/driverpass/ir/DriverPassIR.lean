import ArtifactIR

/-! Auto-generated from examples/driverpass/ir/driverpass.ir.json (IR digest f06cc1f031603334).
DO NOT EDIT: python3 packages/ir/scripts/irc.py lean --write examples/driverpass/ir/driverpass.ir.json ...
The theorem below is checked by the Lean kernel by evaluation (`decide`):
it establishes that this IR instance satisfies `wellFormed`. -/

open Architecton.IR

def driverPass : Model where
  goals := [
    { id := "G0", parent := none, provenance := [⟨"ART-BRD", "make reservations for customers", .source⟩, ⟨"ART-GOALS", "**G0:**", .design⟩] },
    { id := "G1", parent := some "G0", provenance := [⟨"ART-GOALS", "G1 (BR-001)", .design⟩] },
    { id := "G2", parent := some "G0", provenance := [⟨"ART-GOALS", "G2 (BR-002)", .design⟩] },
    { id := "G3", parent := some "G0", provenance := [⟨"ART-GOALS", "G3 (BR-003)", .design⟩] },
    { id := "G4", parent := some "G0", provenance := [⟨"ART-GOALS", "G4 (SR-001)", .design⟩] },
    { id := "G5", parent := some "G0", provenance := [⟨"ART-GOALS", "G5 (SR-002)", .design⟩] },
    { id := "G6", parent := some "G0", provenance := [⟨"ART-GOALS", "G6 (SR-003)", .design⟩] }
  ]
  requirements := [
    { id := "BR-001", kind := .business, goals := ["G1"], provenance := [⟨"ART-REFINEMENT", "theorem ir_refines_allocate", .proof⟩, ⟨"ART-RUST-ORACLE", "fn rust_matches_ir_oracle", .test⟩, ⟨"ART-POLICY", "BR-001", .source⟩, ⟨"ART-LEAN-PROOFS", "theorem offDuty_denied", .proof⟩, ⟨"ART-RUST-DOMAIN", "pub fn allocate", .implementation⟩, ⟨"ART-SCENARIOS", "off_duty", .test⟩] },
    { id := "BR-002", kind := .business, goals := ["G2"], provenance := [⟨"ART-REFINEMENT", "theorem ir_refines_allocate", .proof⟩, ⟨"ART-RUST-ORACLE", "fn rust_matches_ir_oracle", .test⟩, ⟨"ART-POLICY", "BR-002", .source⟩, ⟨"ART-LEAN-PROOFS", "theorem duplicate_denied", .proof⟩, ⟨"ART-RUST-DOMAIN", "pub fn allocate", .implementation⟩, ⟨"ART-SCENARIOS", "duplicate", .test⟩] },
    { id := "BR-003", kind := .business, goals := ["G3"], provenance := [⟨"ART-REFINEMENT", "theorem ir_refines_allocate", .proof⟩, ⟨"ART-RUST-ORACLE", "fn rust_matches_ir_oracle", .test⟩, ⟨"ART-POLICY", "BR-003", .source⟩, ⟨"ART-LEAN-PROOFS", "theorem accepted_prepends_slot", .proof⟩, ⟨"ART-RUST-DOMAIN", "pub fn allocate", .implementation⟩, ⟨"ART-SCENARIOS", "accepted", .test⟩] },
    { id := "SR-001", kind := .nonfunctional, goals := ["G4"], provenance := [⟨"ART-LEAN-TX", "theorem tx_rejected_keeps_allocations", .proof⟩, ⟨"ART-RUST-TX-TESTS", "fn every_injected_fault_rolls_back_completely", .test⟩, ⟨"ART-REFINEMENT", "theorem ir_refines_allocate", .proof⟩, ⟨"ART-RUST-ORACLE", "fn rust_matches_ir_oracle", .test⟩, ⟨"ART-POLICY", "SR-001", .source⟩, ⟨"ART-LEAN-PROOFS", "theorem rejected_preserves_roster", .proof⟩, ⟨"ART-RUST-DOMAIN", "pub fn allocate", .implementation⟩] },
    { id := "SR-002", kind := .nonfunctional, goals := ["G5"], provenance := [⟨"ART-LEAN-TX", "theorem run_no_double_booking", .proof⟩, ⟨"ART-RUST-SERVICE", "TransactionBehavior::Immediate", .implementation⟩, ⟨"ART-RUST-TX-TESTS", "fn concurrent_connections_never_double_book", .test⟩, ⟨"ART-RUST-TX-TESTS", "fn all_request_sequences_up_to_length_4_match_reference", .test⟩, ⟨"ART-POLICY", "SR-002", .source⟩, ⟨"ART-SEQUENCE-UML", "BEGIN IMMEDIATE", .design⟩, ⟨"ART-RUST-API", "async fn assign_slot", .implementation⟩, ⟨"ART-SMOKE", "\"POST\", \"/api/v1/instructors/7/slots\"", .test⟩] },
    { id := "SR-003", kind := .nonfunctional, goals := ["G6"], provenance := [⟨"ART-LEAN-TX", "theorem tx_audits_exactly_once", .proof⟩, ⟨"ART-RUST-SERVICE", "INSERT INTO allocation_audit", .implementation⟩, ⟨"ART-RUST-TX-TESTS", "fn each_committed_request_audits_exactly_once", .test⟩, ⟨"ART-POLICY", "SR-003", .source⟩, ⟨"ART-RUST-API", "audit", .implementation⟩, ⟨"ART-SMOKE", "audit", .test⟩] }
  ]
  risks := [
    { id := "RK-001", status := .mitigated, mitigatedBy := ["SR-002"], provenance := [⟨"ART-GOALS", "G5 (SR-002)", .design⟩] },
    { id := "RK-002", status := .mitigated, mitigatedBy := ["SR-001", "BR-001", "BR-002"], provenance := [⟨"ART-GOALS", "G4 (SR-001)", .design⟩] },
    { id := "RK-003", status := .mitigated, mitigatedBy := ["SR-003"], provenance := [⟨"ART-GOALS", "G6 (SR-003)", .design⟩] },
    { id := "RK-004", status := .accepted, mitigatedBy := [], provenance := [⟨"ART-GOALS", "**Deliberate scope:**", .design⟩] },
    { id := "RK-005", status := .open, mitigatedBy := [], provenance := [⟨"ART-GOALS", "It does **not** prove the above relation", .design⟩] }
  ]
  stateVars := [("offDuty", .bool), ("slots", .natList)]
  transitions := [
    { id := "TR-assign_slot",
        params := [("slot", .nat)],
        guards := [
          { requirement := "BR-001", cond := (.var "offDuty"), outcome := "off_duty" },
          { requirement := "BR-002", cond := (.contains (.var "slots") (.param "slot")), outcome := "duplicate" }
        ],
        otherwiseRequirement := "BR-003",
        otherwiseOutcome := "accepted",
        effect := [
          { var := "slots", value := (.cons (.param "slot") (.var "slots")) }
        ] }
  ]
  invariants := [
    { id := "INV-001", requirement := "BR-002", body := (.nodup (.var "slots")) }
  ]
  artifacts := [
    { id := "ART-BRD", path := "CS 255 Business Requirements Document Template.docx", sha256 := "8f0d11f525851f969d8fe9664c53dad67f1601766369958b73a1f235ad94cb87" },
    { id := "ART-POLICY", path := "examples/driverpass/requirements/policy.json", sha256 := "b1590964089b173ca40acce4e2be1c0c1eb7aa2acbb0efaa4f76582390f0eab3" },
    { id := "ART-GOALS", path := "examples/driverpass/design/goal-refinement.md", sha256 := "d5842de7dd10e4acefeec823ac63f02b277d11043facc3bd0fa921502604d7b3" },
    { id := "ART-DOMAIN-UML", path := "examples/driverpass/design/domain.puml", sha256 := "17df7ad16658ecb41939d8c1ea94219f6d9304cc81f380da4c38edca274a8141" },
    { id := "ART-SEQUENCE-UML", path := "examples/driverpass/design/sequence.puml", sha256 := "5583129230571cd4640140146f6711e3c840e12d45916f34a4a0caa853a717f3" },
    { id := "ART-LEAN-SPEC", path := "examples/driverpass/formal/DriverPass.lean", sha256 := "450346a32ac2feb712834de529c3d3d2226969e11261dc5b162738b49782ef0a" },
    { id := "ART-LEAN-PROOFS", path := "examples/driverpass/formal/Proofs.lean", sha256 := "645b866b92774837bdfd8c80a30c053245c6d776742754985aad24f05da83f2a" },
    { id := "ART-RUST-DOMAIN", path := "examples/driverpass/backend/src/domain.rs", sha256 := "ce92a0c2005c99603ffe8322c327c889a36c132c2cc8d2a45d47f046f2379211" },
    { id := "ART-RUST-API", path := "examples/driverpass/backend/src/main.rs", sha256 := "c45810d6c014c53ffb60b08c28e0f0067eb9f897ede62ce09119c72eb4fd4d39" },
    { id := "ART-SCENARIOS", path := "examples/driverpass/contracts/scenarios.json", sha256 := "3d0a02f0fad70f8eb3f18e8d4e125289b13ac8ecc17f8fc68b647e87a7846bc4" },
    { id := "ART-SMOKE", path := "examples/driverpass/scripts/smoke.py", sha256 := "2ea656ed0e188c73a0add4755c3d69b0effa06f720144fd560892eb20832fb95" },
    { id := "ART-REFINEMENT", path := "examples/driverpass/ir/Refinement.lean", sha256 := "2c9fb2dc879ab28abc6c2e816e2c3913dac71500b4d7b781cf6dc07aa7904b3f" },
    { id := "ART-RUST-ORACLE", path := "examples/driverpass/backend/tests/oracle.rs", sha256 := "42df6ef5214665b85fada3c557090efe6204f14bb5a88fb7e02794073ff1297f" },
    { id := "ART-LEAN-TX", path := "examples/driverpass/formal/Transactions.lean", sha256 := "38a4fe5b1993f5f72d2403b0c6aec3a3a6ff94c2e288232f2a1c06e32ba197fc" },
    { id := "ART-RUST-SERVICE", path := "examples/driverpass/backend/src/service.rs", sha256 := "406f44b1ea5d9445e0354933172c046679e76ca2695153562d925e072d79ce89" },
    { id := "ART-RUST-TX-TESTS", path := "examples/driverpass/backend/tests/transactions.rs", sha256 := "fbea7f33dba08960b8b2079858d5f0997e3b1811a3d69b49c973eebfbcfc1707" }
  ]

theorem driverPass_wellFormed : wellFormed driverPass = true := by decide

/-- Consequence for this instance: every guard of every transition evaluates
to a Boolean in every state and parameter environment that conforms to the
declared types. -/
theorem driverPass_guards_evaluate {tr : Transition} (htr : tr ∈ driverPass.transitions)
    {g : Guard} (hg : g ∈ tr.guards) {σ ρ : Env}
    (hσ : Conforms driverPass.stateVars σ) (hρ : Conforms tr.params ρ) :
    ∃ b, eval σ ρ g.cond = some (.bool b) :=
  wf_guard_evaluates driverPass_wellFormed htr hg hσ hρ
