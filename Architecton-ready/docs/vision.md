# Architecton research vision

## Research question

Can a change to a human business intention be expressed in a typed semantic model and then transformed through design, proof and execution with explicit, machine-checkable evidence of semantics preservation?

## Stages

1. **Intent and elicitation:** stakeholder goals, BRD/SRS, constraints; ambiguity is resolved through a human review gate.
2. **Requirements semantics / IR:** typed state variables, commands, predicates, priorities, transitions, preconditions, postconditions, invariants and provenance IDs.
3. **Architectural and detailed design:** UML/SysML/ArchiMate views, contracts, deployment boundaries and traceability.
4. **Formalization:** Lean 4 definitions, propositions, theorems and explicit assumptions.
5. **Mechanization and verification:** proof obligations, termination/safety properties, simulation relations, model exploration and counterexamples.
6. **Implementation and infrastructure:** Rust domain logic, REST APIs, transactions, eventing, build/test/deploy.
7. **Runtime conformance:** differential tests, invariant monitoring, audit, evidence manifests and CI/CD release gates.

## Milestones

- **M0 — DriverPass vertical slice:** narrow deterministic decision table; Lean and Rust adapters; shared scenarios; SQLite/Axum; local container.
- **M1 — typed IR:** a versioned schema with type-checking and checked canonicalization of requirements semantics.
- **M2 — multiple model projections:** UML, SysML and ArchiMate exports with traceable transformation contracts.
- **M3 — proofs of refinement:** prove that target language semantics simulate source transition semantics over a specified state domain.
- **M4 — infrastructure verification:** authorization, transaction isolation, failure, retry, idempotency and concurrency models.
- **M5 — assurance evidence:** proof certificates, artifacts, reproducible releases and continuous production checking.

This is a research agenda. No stage beyond M0 is implemented merely because it appears in the diagram.
