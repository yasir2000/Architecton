# Formal RUP lifecycle — Architecton M1 process slice

This module implements a **small, mathematically specified process model** on top of the Rational Unified Process (RUP): Inception, Elaboration, Construction, Transition, and overlapping engineering workflows. It does *not* replace UML/ArchiMate or prove existing documents correct. It adds an inspectable, reviewable verification layer over their lifecycle.

## Intent → policy → model → proof → check

```text
RUP concept + stakeholder assurance needs
       ↓ analyst reviews LC-001 .. LC-008
requirements/policy.json  (phase gates and evidence vocabulary)
       ↓ deterministic closed-vocabulary generator
formal/Policy.lean (source-of-truth gate definition)
       ↓ imports verified domain types
formal/ArchitectonLifecycle.lean  → formal/StateMachine.lean
                                           ↓
                              formal/Proofs.lean
                              formal/Scenarios.lean
       ↓
Python scenario interpreter + GitHub Actions Lean kernel check
       ↓
DriverPass example lifecycle plan: examples/driverpass/lifecycle/iteration-plan.md
```

The policy is deliberately limited to **one controlled requirements baseline at a time**. A change to requirements increments the revision, archives the old attestations and clears current evidence. An ordinary iteration does not invalidate an unchanged baseline. Multiple RUP iterations may occur inside one phase.

## Gate table

| Current phase | Minimum evidence before `promote` | Next phase |
|---|---|---|
| Inception | `requirementsReviewed`, `traceabilityReviewed` | Elaboration |
| Elaboration | `designReviewed`, `formalSpecificationChecked` | Construction |
| Construction | `proofChecked`, `conformancePassed`, `artifactBuilt` | Transition |
| Transition | none; no successor | No promotion |

Additional `deploymentValidated` evidence can be recorded during Transition, but cannot establish anything about production reliability or security unless its external producer does.

## Trust, assurance, limitations

- The Lean state-machine theorems establish invariants **conditional on the formal transition semantics** and trusted `recordValidated` events.
- In this PoC, `recordValidated` accepts a token without validating artifact hashes, certificate signatures or provenance. Accordingly, this is **not** an enforcement engine for a production pipeline.
- Passing the Lean proofs does **not** establish semantic preservation of natural-language requirements, UML diagrams, Rust implementations, CI scripts or deployed workloads.
- RUP curves in the supplied reference diagram illustrate *relative effort* by workflow; this model proves only workflow availability and gate conditions, not time/effort optimization or staffing.
- A revision resets every gate, which is a conservative safety policy. Future releases should use fine-grained dependency-based invalidation and refinement proof reuse.

See [methodology](../../docs/methodology-rup-formal.md), [traceability table](requirements/traceability.csv), and [workflow diagrams](design/phase-state-machine.puml).

## Run checks

From `packages/lifecycle/`:

```bash
python3 scripts/generate_policy.py --check
python3 scripts/verify_scenarios.py

# Requires Lean 4.35.0 (specified in lean-toolchain):
export LEAN_PATH=formal
lean -o formal/ArchitectonLifecycle.olean formal/ArchitectonLifecycle.lean
lean -o formal/Policy.olean formal/Policy.lean
lean -o formal/StateMachine.olean formal/StateMachine.lean
lean formal/Proofs.lean
lean formal/Scenarios.lean
```

To intentionally regenerate the phase-gate definition after **reviewing** a policy change:

```bash
python3 scripts/generate_policy.py --write
```

CI checks the generated file is in sync, checks 12 Python reference scenarios and 1,024 bounded state configurations, then kernel-checks the Lean model and theorems when a GitHub Actions runner is available.
