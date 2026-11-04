# What is formally verified in the DriverPass PoC?

| Claim | Verification mechanism | Scope |
|---|---|---|
| Off-duty denial | Lean theorem | Pure Lean transition |
| Duplicate denial | Lean theorem | Pure Lean transition, same instructor |
| No roster mutation on rejection | Lean theorem | Pure Lean transition |
| Successful assignment prepends requested slot | Lean theorem | Pure Lean transition |
| Generated files reflect the normalized policy | Python generation consistency check | Fixed policy vocabulary, not general BRD translation |
| Rust matches examples | Shared scenario and bounded-domain Rust tests | Finite examples, not universal Lean↔Rust proof |
| API handles scenarios and audit | HTTP/SQLite smoke test | Single-process local database example |
| Cross-language observational equivalence | **Not proved** | Needs a refinement/simulation proof |
| Correctness of compiler, SQLite, OS, network or Docker | **Not proved** | Outside trusted model boundary |
| Authentication and authorization | **Not implemented** | Do not expose the example publicly |

Lean proof files contain no project-specific axioms or `sorry` by design. Proofs are authoritative only if successfully checked with the pinned Lean toolchain. A GitHub Actions workflow is provided to run the checks; this staging environment could only run the Python generator and scenario validator.

The sample API is educational. It lacks authentication, authorization and abuse protection, and must remain loopback-only.

## Formal RUP lifecycle assurance (separate from DriverPass domain proofs)

The `packages/lifecycle` module defines Lean 4 theorem obligations for safe promotions, no phase skipping, blocked-state immutability, baseline revision invalidation, and the construction release gate. It includes 12 Python reference scenarios and a bounded sweep of 1,024 phase/evidence states. **Theorem proofs are not kernel-confirmed until the pinned Lean CI job completes successfully.**

An external authority is assumed to provide trustworthy `recordValidated` evidence. The module itself neither authenticates the attester nor checks proofs, source hashes, signed attestations, build provenance, deployment health, or cross-language compiler refinement. The model is an educational verification process, not a production compliance controller.
