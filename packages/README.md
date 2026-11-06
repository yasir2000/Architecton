# Architecton packages

Shared tooling for the [research roadmap](../README.md#research-roadmap-next-work-packages). The end-to-end working slice is in `../examples/driverpass`.

## Implemented packages

- [`ir/`](ir/README.md): typed artifact IR v1. Goals, requirements, risks, typed state transitions, invariants, provenance anchors and artifact hashes, checked by a Python validator and by the Lean kernel.
- [`design/`](design/README.md): design refinements. UML state, sequence and class diagrams and a typed ArchiMate model, checked against the formal models, IR and code, with a Lean proof that the phase state diagram matches the lifecycle model.
- [`ledger/`](ledger/README.md): trusted evidence ledger. Content-addressed, SSH-signed check results with a dependency graph, revocation and scoped re-verification, backed by a Lean theorem on revocation scope.
- [`lifecycle/`](lifecycle/README.md): Lean-based RUP lifecycle, generated policy gates, proof obligations, scenarios and CI.
- [`temporal/`](temporal/README.md): Lean temporal core. LTL with infinite and finite semantics, safety/co-safety bridge theorems, proof rules and fairness, with kernel-checked temporal properties of the lifecycle and DriverPass models.

## Planned, not yet implemented

Runtime trace monitoring, a TLA+ concurrency model and distributed consistency (the rest of temporal/runtime verification). (Cross-language conformance is implemented for DriverPass inside `ir/` and `examples/driverpass/`.)
