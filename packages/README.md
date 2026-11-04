# Architecton packages

Shared tooling for the [research roadmap](../README.md#research-roadmap-next-work-packages). The end-to-end working slice is in `../examples/driverpass`.

## Implemented packages

- [`ir/`](ir/README.md): typed artifact IR v1. Goals, requirements, risks, typed state transitions, invariants, provenance anchors and artifact hashes, checked by a Python validator and by the Lean kernel.
- [`ledger/`](ledger/README.md): trusted evidence ledger. Content-addressed, SSH-signed check results with a dependency graph, revocation and scoped re-verification, backed by a Lean theorem on revocation scope.
- [`lifecycle/`](lifecycle/README.md): Lean-based RUP lifecycle, generated policy gates, proof obligations, scenarios and CI.

## Planned, not yet implemented

Design refinements, cross-language conformance (model-to-code refinement), and temporal/runtime verification.
