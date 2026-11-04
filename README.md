# Architecton (ἀρχιτέκτων)

**From human intentions to verifiable executable systems.**

Architecton explores semantics-preserving refinement from stakeholder intentions, business and system requirements, and design models to mechanized formal specifications, kernel-checked proofs, executable services, infrastructure, and runtime evidence.

> **Status: research proof of concept, not a verified production system.** The runnable example is deliberately narrow. It proves properties of a Lean 4 *model*; matching a compiled implementation and its deployment to that model is separately tested, not universally proved.

## Engineering pipeline

```text
Human intentions, BRD, SRS, goals (reviewed by analyst)
   ↓
Versioned semantic decision model / typed IR subset
   ├── UML design views and ArchiMate-inspired mapping
   ├── Lean 4 formal transition + invariants + proof obligations
   └── Rust domain transition + shared behavioral scenarios
                              ↓
                       Axum REST API
                              ↓
               SQLite IMMEDIATE transactions + audit
                              ↓
                 Docker image + CI + smoke tests
```


## Formally governed RUP lifecycle (new process-level PoC)

Architecton extends the four RUP phases—**Inception, Elaboration, Construction, Transition**—with continuous formal specification, proof obligations, model verification, and explicit **evidence-gated iteration**. The cross-cutting verification workflow operates in every phase rather than only after implementation.

- [Formal RUP methodology](docs/methodology-rup-formal.md) and [DriverPass iteration plan](examples/driverpass/lifecycle/iteration-plan.md).
- [Lifecycle specification, Lean theorems and scenarios](packages/lifecycle/README.md).
- [Phase-gate source policy](packages/lifecycle/requirements/policy.json), generated [Lean policy](packages/lifecycle/formal/Policy.lean), and [workflow diagrams](packages/lifecycle/design/phase-state-machine.puml).
- [Lifecycle CI checks](.github/workflows/verify-lifecycle.yml) use Lean kernel checking plus 12 reference scenarios and a 1,024-state bounded sweep.

**Assurance boundary:** Lifecycle theorems prove properties of the abstract process model *assuming trusted verification attestations*. They do not prove that external requirements, designs, binaries, CI jobs, or deployed systems are correct. Changing requirements archives prior approvals and clears current verification evidence.

## Working example: DriverPass

The first vertical slice is an **instructor/lesson slot assignment workflow**, linked to the provided DriverPass business and UML system design documents. It examines a small set of selected scheduling rules, not all of DriverPass's functionality.

- [DriverPass implementation guide](examples/driverpass/README.md)
- [Policy decision table](examples/driverpass/requirements/policy.json)
- [Requirement-to-artifact traceability](examples/driverpass/requirements/traceability.csv)
- [Lean definitions](examples/driverpass/formal/DriverPass.lean) and [theorems](examples/driverpass/formal/Proofs.lean)
- [Rust API](examples/driverpass/backend/src/main.rs)
- [Automated verification checks](.github/workflows/verify-driverpass.yml)

### Quick checks

```bash
cd examples/driverpass
python3 scripts/generate.py --check
python3 scripts/check_contracts.py
export LEAN_PATH=formal
lean -o formal/DriverPass.olean formal/DriverPass.lean
lean formal/Proofs.lean
lean formal/Scenarios.lean
cargo test --manifest-path backend/Cargo.toml
cargo run --manifest-path backend/Cargo.toml
```

Requires Python 3, Lean 4 (pinned in `lean-toolchain`), and Rust/Cargo. See the detailed guide for API examples and Docker usage. Run the Docker commands from `examples/driverpass`, because the Compose build context is relative to that directory.

## Repository structure

```text
Architecton/
  docs/                          Vision, assurance boundary, milestones
  packages/lifecycle/             Formal RUP methodology and Lean phase-gate verification
  packages/                      Future semantic IR/refinement tooling
  examples/driverpass/
    requirements/                Normalized policy and traceability
    design/                      Goals, UML and ArchiMate mapping
    formal/                      Lean 4 model, scenarios and theorems
    backend/                     Rust domain logic and Axum/SQLite service
    contracts/                   Shared scenarios, OpenAPI
    scripts/                     Generation, validation and smoke testing
    infra/                       Dockerfile and Compose
  .github/workflows/             CI checks
```

## Existing BRD, UML design, and broader Lean formalizations

The original source artifacts are preserved at the repository root:

- [CS 255 Business Requirements Document](CS%20255%20Business%20Requirements%20Document%20Template.docx)
- [CS 255 System Design Document](CS%20255%20System%20Design%20Document%20Template.docx)
- [DriverPass.lean](DriverPass.lean) — broader BRD formalization
- [DriverPassDesign.lean](DriverPassDesign.lean) — UML/design formalization

These two pre-existing Lean files are complementary to, but independent of, the **narrow generated instructor-slot assignment example**. Their entire theorem sets are not covered by the example's verification workflow; see [source integration status](docs/source-integration.md).

## Principle

**Do not equate model-level formal proofs with verified deployed software.** Every claimed assurance must identify its assumptions, trusted computing base, coverage and refinement boundary. See [assurance limits](docs/assurance.md) and the [research roadmap](docs/vision.md).

_ἀρχιτέκτων_: the master builder, responsible for unifying vision, structural design and execution.
