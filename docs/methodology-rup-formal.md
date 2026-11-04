# Architecton methodology: formally governed iterative engineering (RUP extension)

## Purpose and provenance

The reference RUP illustration shows four *phases* (**Inception, Elaboration, Construction, Transition**), iterative increments, and overlapping workflows (business modeling, requirements, analysis/design, implementation, test, deployment, configuration/change management, project management, and environment). The colored effort curves indicate that a workflow can remain active across phases; RUP is **not** a sequential waterfall.

Architecton retains those concepts, and introduces a **cross-cutting formal verification workflow** plus explicit machine-checkable phase-gate contracts, requirement-to-design traceability, design-to-model refinement obligations, and evidence from implementation and runtime.

> This document is a proposed Architecton extension to RUP, not a claim that standard RUP requires Lean 4 or these particular evidence gates.

## Layered semantic engineering cycle

For each baseline, iteration and increment:

1. **Stakeholder intention / business modeling.** Acquire business goals, stakeholder scenarios, constraints, risks and acceptance criteria; capture provenance and ambiguities (KAOS, i*, GRL may inform elicitation).
2. **Requirements formalization.** Normalize BRD/SRS into typed predicates, contracts, transitions, priorities, invariants, temporal constraints and named assumptions. The human-approved semantics become the reference for later checks.
3. **Design elaboration.** Relate UML, SysML and ArchiMate views to the semantic intermediate representation (IR). Class/entity mappings, use-case pre/postconditions, state machines, sequences and architecture boundaries must carry typed trace links.
4. **Mechanization.** Translate supported constructs into Lean 4 (or appropriate logics/tools), stating decidability/termination conditions and proof obligations, not inventing unsupported semantics.
5. **Proof.** Discharge safety/refinement obligations by Lean kernel checking, model checking, SMT, or explicit counterexamples; label bounded tests distinctly.
6. **Construction.** Generate or implement Rust/services/DB schemas/infrastructure under versioned contracts. Connect executable observable behavior to the formal reference model through simulations, differential tests and run-time assertions.
7. **Transition.** Produce signed/traceable verification evidence, build manifests, deployment validation and monitoring rules. Preserve exact artifact revisions, assumptions, test results, build digests, and proof status.
8. **Feedback.** Every material requirement or model change invalidates downstream evidence as needed; reopen the affected refinement obligations and repeat the cycle.

This is continuous: requirements, architecture, verification and testing can all recur late in a project.

## RUP phases: deliverables, risks and gated commitments

| Phase | Typical activities (overlap is expected) | Model and evidence gate | Exit risk that remains |
|---|---|---|---|
| Inception | Business case, goals, stakeholders, critical use cases, scope, requirements baseline | Human-approved requirement semantics and traceability (`requirementsReviewed`, `traceabilityReviewed`) | Misinterpreted intent and missing requirements |
| Elaboration | Executable architecture skeleton, UML/SysML/ArchiMate views, formal contracts, proof architecture | Reviewed design and mechanized specifications (`designReviewed`, `formalSpecificationChecked`) | Design IR mapping may not be semantics preserving |
| Construction | Incremental implementation, compilation, proofs, tests, attack/failure exploration | Kernel-checked theorems, conformance results and reproducible build (`proofChecked`, `conformancePassed`, `artifactBuilt`) | Compiler/runtime/OS/DB correctness is not formally established |
| Transition | Pilot operations, installation, performance, monitoring, user acceptance, release | Operational `deploymentValidated` evidence (not modeled as a forward phase promotion) | Real-world performance, safety and security require external verification |

## Process-level formal semantics (implemented)

**Versioned state** is `ProcessState = (phase, iteration, revision, verified, archive)`.

**Actions** are `recordValidated(evidence)`, `iterate`, `promote`, and `reviseRequirements`. `recordValidated` is **modeled as a trusted external validation event**, not as a user-controlled API. Phases have explicit successors, so a successful `promote` never skips one. A blocked promotion returns its original state. An `iterate` increases the iteration counter and retains the current specification revision and its valid evidence. A requirements revision increments the baseline revision, archives the old evidence, clears current evidence, and returns to Inception.

For a state `s`, write `Gate(s)` for the conjunction of evidence required to promote out of `s.phase`, and `step(s,c) = (s', outcome)` for the command transition.

### Proven proof obligations, conditional on the model

- **LC-001, phase-gate soundness:** `step(s,promote).outcome = accepted ⇒ Gate(s)`.
- **LC-002, no phase skipping:** successful `promote` implies `s'.phase = nextPhase(s.phase)`.
- **LC-003, nonmutation on rejection:** blocked promotion implies `s' = s`.
- **LC-004, iterative preservation:** for unchanged requirements, iteration preserves phase and validated evidence.
- **LC-005, evidence invalidation:** requirements revision clears current evidence and restarts Inception, while archiving previous evidence.
- **LC-006, release-gate safety:** promoting Construction → Transition requires `proofChecked ∧ conformancePassed ∧ artifactBuilt` in the current baseline.
- **LC-007, terminal phase:** Transition cannot be promoted to a nonexistent successor.
- **LC-008, overlapping workflows:** every RUP workflow, including formal verification, can be performed in any phase (availability, **not** effort or completeness).

The actual Lean definitions and theorem statements live under [`packages/lifecycle/formal/`](../packages/lifecycle/formal/). `Policy.lean` is generated from a closed-vocabulary [`policy.json`](../packages/lifecycle/requirements/policy.json); all other theorem statements are independently maintained.

## Semantic preservation obligations (research backlog)

Future process formalization should attach a proof *per transformation* rather than merely proving the lifecycle gate mechanism:

```text
Requirements IR R
    | transform F with explicit assumptions A
    v
Design IR D
    | refinement G; simulation relation Rel_RD
    v
Lean executable model M
    | compiler/backend H; simulation relation Rel_MC
    v
Rust/service semantics C
    | transactional deployment relation Rel_CR
    v
Observable runtime traces T
```

For a supported transformation `F : R → D`, state a relation such as

`∀ r, WellFormed(r) ∧ A(r) → Refines(r, F(r))`.

For an implementation `C`, establish an observational trace simulation, with explicit environment and concurrency assumptions:

`∀ c ∈ Reachable(C), ∃ m ∈ Reachable(M), Rel_MC(m,c)`.

The finite Python scenarios in the current PoC are **not** proofs of these quantified refinement relations. Tool claims must distinguish *proof checked*, *bounded model checked*, *tested*, *reviewed*, and *unverified* evidence states.

## Planned next increments

1. **Typed artifact IR:** goals, requirement statements, risk identifiers, typed state transitions, invariants, provenance anchors and artifact hashes.
2. **Trusted evidence ledger:** content-addressed inputs; CI-signed attestations; immutable proof results; validator identity; dependency DAG; revocation and scoped re-verification.
3. **Design refinements:** well-formed UML activity/state/sequence subset, executable semantics, ArchiMate architecture constraints and trace relations.
4. **Cross-language conformance:** Lean ↔ Rust reference equivalence, SQLite transaction models, test oracle generation, failure injection and systematic bounded checking.
5. **Temporal/runtime verification:** LTL/TLA+ transition properties, deadlock/liveness/fairness, distributed consistency and monitored production traces.

This methodology distinguishes **formal methods for the engineering process** from **formal proofs of the engineered product**. Both are required for Architecton's long-term objective.
