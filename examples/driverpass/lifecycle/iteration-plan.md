# DriverPass through proof-oriented RUP iterations

This is an **illustrative process plan**, not a claim that all required evidence is available. The original BRD, UML design document, `DriverPass.lean`, and `DriverPassDesign.lean` remain authoritative source artifacts in Architecton's repository root. The narrow instructor-slot example is a selected refinement, not a full translation of those documents.

## Inception — Baseline B0: assignment rules

- Select business goal: prevent invalid lesson-slot allocations.
- Human-review ambiguity: off-duty instructor restriction and duplicate-slot prohibition are explicit **PoC policy decisions**, not a universal automatic consequence of every BRD statement.
- Artifacts: `../requirements/policy.json`, `../requirements/traceability.csv`, and `../design/goal-refinement.md`.
- Gate: approve requirements semantics and inspect source-to-policy trace links.
- No Lean proof validates the English-to-policy interpretation.

## Elaboration — Iterations E1 and E2

- E1: map instructor, roster, slot and allocation decisions to UML/domain types.
- E2: establish Lean transition semantics in `../formal/DriverPass.lean`; derive proof obligations in `../formal/Proofs.lean`.
- Gate: model reviewed, formal spec checked by Lean kernel, assumptions and open obligations documented.
- Broader UML/BRD Lean formalizations in repository root are complementary and not automatically certified by this iteration's tests.

## Construction — Iterations C1 and C2

- C1: Rust domain kernel implements the accepted/rejected roster transition.
- C2: Axum handlers, SQLite IMMEDIATE transactions, audit log, OpenAPI contract, and shared scenarios.
- Gate: proof checking of the pure Lean transition, Rust/Python finite conformance tests, and artifact build evidence.
- Critical open proof: **universal Lean-to-Rust refinement is not established**; end-to-end DB/HTTP correctness is tested only.

## Transition — Iteration T1

- Local container smoke tests, documented API acceptance tests, and operator-facing monitoring.
- Gate: operational validation, security review and deployment attestations (currently planned, not proved).
- Explicit blocker for public launch: sample API lacks authentication and authorization.

## Change-control scenario for the research demonstration

Suppose new stakeholder intent changes slot identity from a `Nat` to an interval with start/end times, prohibiting overlaps across instructors. This is a **requirements revision** rather than a cosmetic iteration:

1. Archive B0's proofs and validations; increment baseline revision.
2. Re-elicit and approve the revised scheduling semantics.
3. Update the structural UML model and formal transition type.
4. Reprove off-duty, overlap, idempotency and rejected-state invariants.
5. Re-run conformance, transactional concurrency and deployment checks.

Architecton's [`packages/lifecycle`](../../../packages/lifecycle/) formalization proves that the *abstract process state* requires fresh phase-gate evidence following such a revision. It does **not** automatically detect changes in arbitrary files or revoke real CI attestations: those need a trusted artifact-evidence service.
