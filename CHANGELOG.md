# Changelog

All notable changes to Architecton are recorded here. The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The project has no tagged releases yet.

## [Unreleased]

### Added

- Project branding: logo, brand guide, contributor and security docs, issue and PR templates.
- Design refinements: UML state, sequence and class diagrams and a typed ArchiMate model, checked against the formal models, IR and code. A Lean proof shows the phase state diagram matches the lifecycle model.
- Signed evidence ledger with content-addressed results, a dependency graph and revocation, with a Lean theorem on revocation scope.
- Lean model of the SQLite slot transaction (atomicity, exactly-once audit, no double booking), plus Rust fault-injection and race tests.
- Lean proof that the DriverPass IR transition refines `allocate`, and 850 kernel-checked oracle vectors replayed against Rust.
- Typed artifact IR v1 with Lean semantics and a DriverPass instance.
- Formal RUP engineering lifecycle with generated policy gates and proof obligations.
- DriverPass instructor-slot allocation vertical slice: policy, Lean model and proofs, Rust domain and Axum/SQLite service, Docker and CI.
- Formalization of the DriverPass BRD and design documents.
- Architecton Source-Available License 1.0.

### Fixed

- DriverPass and lifecycle checks now pass on Lean 4.35 and Windows.
