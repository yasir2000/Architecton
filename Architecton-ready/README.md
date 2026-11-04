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
  packages/                      Future shared semantic IR/refinement tooling
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

## Principle

**Do not equate model-level formal proofs with verified deployed software.** Every claimed assurance must identify its assumptions, trusted computing base, coverage and refinement boundary. See [assurance limits](docs/assurance.md) and the [research roadmap](docs/vision.md).

_ἀρχιτέκτων_: the master builder, responsible for unifying vision, structural design and execution.
