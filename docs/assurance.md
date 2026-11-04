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
| Transaction step order is correct (SR-001–SR-003): all-or-nothing on every fault, exactly one audit row per decision, response roster equals stored roster, no double booking under any serial order | Lean theorems in [Transactions.lean](../examples/driverpass/formal/Transactions.lean) | Lean model of the code's steps; **assumes** (A1) SQLite rolls back aborted transactions and (A2) `BEGIN IMMEDIATE` serializes writers |
| A1 and A2 hold for the real code | [transactions.rs](../examples/driverpass/backend/tests/transactions.rs): fault injection at all 4 steps, 8 and 6 concurrent connections, all 341 request sequences up to length 4 against a reference model | Tests on one machine with real SQLite; a mutant using deferred transactions fails the concurrency tests |
| IR transition computes the Lean `allocate` | Lean theorem `ir_refines_allocate` ([Refinement.lean](../examples/driverpass/ir/Refinement.lean)) | All rosters and slots; Lean model only |
| INV-001 (no slot held twice) is preserved | Lean theorems `allocate_preserves_nodup`, `ir_preserves_inv001` | All rosters and slots; Lean model only |
| Rust agrees with Lean on the oracle | 850 IR-derived vectors, each kernel-checked against Lean ([Oracle.lean](../examples/driverpass/ir/Oracle.lean)), replayed in Rust ([oracle.rs](../examples/driverpass/backend/tests/oracle.rs)) | Bounded: rosters of length ≤ 3 over slots 0–3, requests 0–4 |
| Rust ↔ Lean equivalence for all inputs | **Not proved** | Bounded testing only; Rust `i64` vs Lean `Nat` also differ on negative slots, which the API rejects before `allocate` |
| Correctness of compiler, SQLite, OS, network or Docker | **Not proved** | Outside trusted model boundary |
| Authentication and authorization | **Not implemented** | Do not expose the example publicly |

Lean proof files contain no project-specific axioms or `sorry` by design. Proofs are authoritative only if successfully checked with the pinned Lean toolchain. A GitHub Actions workflow is provided to run the checks; this staging environment could only run the Python generator and scenario validator.

The sample API is educational. It lacks authentication, authorization and abuse protection, and must remain loopback-only.

## Formal RUP lifecycle assurance (separate from DriverPass domain proofs)

The `packages/lifecycle` module defines Lean 4 theorem obligations for safe promotions, no phase skipping, blocked-state immutability, baseline revision invalidation, and the construction release gate. It includes 12 Python reference scenarios and a bounded sweep of 1,024 phase/evidence states. **Theorem proofs are not kernel-confirmed until the pinned Lean CI job completes successfully.**

An external authority is assumed to provide trustworthy `recordValidated` evidence. The module itself neither authenticates the attester nor checks proofs, source hashes, signed attestations, build provenance, deployment health, or cross-language compiler refinement. The model is an educational verification process, not a production compliance controller.
