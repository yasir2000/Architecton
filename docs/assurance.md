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
