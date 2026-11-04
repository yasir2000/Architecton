# Architecton (ἀρχιτέκτων)

**From human intentions to verifiable executable systems.**

Architecton explores semantics-preserving refinement from stakeholder intentions, business and system requirements, and design models to mechanized formal specifications, kernel-checked proofs, executable services, infrastructure, and runtime evidence.

> **Status: research proof of concept, not a verified production system.** The runnable example is deliberately narrow. It proves properties of a Lean 4 *model*; matching a compiled implementation and its deployment to that model is separately tested, not universally proved.

## At a glance

### Why

Requirements, designs, proofs and running code usually drift apart. A business rule written in a BRD gets reinterpreted in a UML diagram, then re-implemented in code, and nobody can show that the deployed system still means what the stakeholder intended. Architecton asks whether that chain can carry **explicit, machine-checkable evidence of semantics preservation** at every step, and is honest about where the evidence stops.

### What

A research proof of concept that links one chain of artifacts end to end:

- stakeholder intentions and requirements (BRD, SRS, goals) normalized into a policy decision table;
- design views (UML, ArchiMate-inspired mapping) and requirement-to-artifact traceability;
- a Lean 4 formal model with kernel-checked theorems (no project-specific axioms or `sorry`);
- a Rust domain implementation and Axum/SQLite REST service checked against the same shared scenarios;
- Docker packaging and CI that re-run every check.

The current working slice is the **DriverPass instructor/lesson slot assignment** workflow. Reusable tooling lives in [packages/](packages/README.md): the typed artifact IR v1 is implemented, while model transformations and refinement proofs are still planned.

### When

- **Now (M0):** the DriverPass vertical slice is implemented and is the only completed milestone.
- **In progress (M1):** the typed artifact IR v1 is implemented and checked on DriverPass; generalizing its type system beyond `Bool`, `Nat` and `List Nat` remains.
- **Next (M2–M5):** multiple model projections, refinement proofs, infrastructure verification and assurance evidence. See the [roadmap](docs/vision.md#milestones).
- **Use it when** you want a worked example of tracing a business rule through formal proof to an executable service, or a starting point for research on requirements-to-code refinement. **Don't use it** as production software: the sample API has no authentication and must stay loopback-only.

### How

1. Analysts review intentions and requirements and resolve ambiguity.
2. The rules are captured once in a normalized policy ([policy.json](examples/driverpass/requirements/policy.json)).
3. A generator derives the Lean and Rust artifacts from that policy and checks they stay consistent.
4. Lean proves the model's properties; Rust tests and HTTP smoke tests check the implementation against shared scenarios.
5. CI ([verify-driverpass.yml](.github/workflows/verify-driverpass.yml)) runs all of it on every change.

The [engineering pipeline](#engineering-pipeline) and [quick checks](#quick-checks) below give the detail; [assurance limits](docs/assurance.md) list what each check does and does not prove.

### Who

- **Author and maintainer:** Yasir Karam ([yasir2000](https://github.com/yasir2000)).
- **Intended readers:** software architects, requirements engineers, formal-methods researchers and students who want to connect business requirements, design models and verified code.
- **Roles in the pipeline:** stakeholders state intentions, an analyst reviews and approves the normalized requirements, and the toolchain (Lean kernel, Rust tests, CI) produces the evidence.

### Where

- **Repository:** [github.com/yasir2000/Architecton](https://github.com/yasir2000/Architecton).
- **Working example:** [examples/driverpass/](examples/driverpass/README.md).
- **Source BRD and design documents:** repository root (see [below](#existing-brd-uml-design-and-broader-lean-formalizations)).
- **Vision, assurance boundary and integration status:** [docs/](docs/).
- **Runtime:** locally, or in a local Docker container from `examples/driverpass`; not meant for public deployment.

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
  packages/ir/                   Typed artifact IR: checker, Lean semantics and proofs
  packages/lifecycle/            Formal RUP methodology and Lean phase-gate verification
  examples/driverpass/
    ir/                          DriverPass IR instance and its generated Lean model
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

## Research roadmap: next work packages

The first item has a working v1. The rest are planned and not yet implemented; see the [milestones](docs/vision.md#milestones).

- **Typed artifact IR** (v1 implemented, see [packages/ir](packages/ir/README.md)): goals, requirement statements, risk identifiers, typed state transitions, invariants, provenance anchors and artifact hashes. The DriverPass slice has a [checked IR instance](examples/driverpass/ir/driverpass.ir.json), and the Lean kernel proves it well-formed.
- **Trusted evidence ledger:** content-addressed inputs; CI-signed attestations; immutable proof results; validator identity; dependency DAG; revocation and scoped re-verification.
- **Design refinements:** well-formed UML activity/state/sequence subset, executable semantics, ArchiMate architecture constraints and trace relations.
- **Cross-language conformance:** Lean ↔ Rust reference equivalence, SQLite transaction models, test oracle generation, failure injection and systematic bounded checking.
- **Temporal/runtime verification:** LTL/TLA+ transition properties, deadlock/liveness/fairness, distributed consistency and monitored production traces.

## Principle

**Do not equate model-level formal proofs with verified deployed software.** Every claimed assurance must identify its assumptions, trusted computing base, coverage and refinement boundary. See [assurance limits](docs/assurance.md) and the [research roadmap](docs/vision.md).

_ἀρχιτέκτων_: the master builder, responsible for unifying vision, structural design and execution.

## License

Copyright (C) 2026 Yasir Karam

Architecton is **source-available, not open source**, under the [Architecton Source-Available License 1.0](LICENSE):

- **Commercial use is not allowed.**
- **Academic use** (teaching, coursework, research, publications) **is not allowed without the author's prior written permission.**
- Viewing and running the code for personal evaluation is allowed. Modifying, redistributing or building on it needs written permission.

To request permission, contact Yasir Karam at [yasirkaram@gmail.com](mailto:yasirkaram@gmail.com).
