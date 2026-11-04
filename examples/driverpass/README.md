# DriverPass: requirement → model → Lean 4 proof → Rust API → SQLite → Docker

**Scope:** Small but genuine engineering proof of concept for a single operation:
**assign a lesson slot to one instructor**. The policy denies allocations for
an off-duty instructor, denies duplicate slots, preserves the roster on failures,
and adds an available slot on success.

> Status of this packaged version: the Python policy generator and contract
> sanity checks were run here. This environment did not provide Lean 4, Rust,
> Cargo, or Docker, so their compilation and integration steps are provided as
> executable commands and CI checks, **not represented as already passing**.

## 1. What is actually transformed?

```text
Stakeholder goal: no invalid lesson assignment
  -> analyst-validated BR-001, BR-002, BR-003, SR-001..SR-003
  -> typed, ordered decision-table model (requirements/policy.json)
     |                         |
     | generator               | generator
     v                         v
  Lean 4 allocate           Rust allocate
     |                         |
  proofs + model cases     Rust semantic scenario tests
                               |
                             Axum REST API
                               |
                    SQLite IMMEDIATE transaction
                     /                    \
               allocations             audit entries
                               |
                        container / CI / HTTP smoke
```

**IMPORTANT**: natural-language intention → normalized policy is still
human-reviewed, because requirement interpretation is not uniquely determined
by wording. The generator is narrowly defined for two ordered predicates plus
one terminal effect; it refuses unsupported semantics instead of inventing
mappings. The user can experiment with policy precedence but unrecognized
policies are deliberately rejected.

## 2. The smallest end-to-end story

**Scenario:** Instructor `7` starts on duty with no slots. The client requests
slot `42`:

- BR-001: is `off_duty = true`? No.
- BR-002: is slot `42` already in this instructor's roster? No.
- BR-003: prepend slot 42 and report `accepted`.
- A transaction inserts allocation (7,42) and an audit record, then commits.
- Client receives HTTP `201` and `{ "decision":"accepted", ... }`.

A repeat request for slot 42 returns HTTP `409` / `duplicate`; the roster
remains `[42]`. Mark the instructor off duty and try slot 43; it returns `409` /
`off_duty`, with the roster still `[42]`. Both rejected attempts are audited.

## 3. Traceability by engineering layer

| Stage | Artifact | Mechanical check |
|---|---|---|
| Business intention / GORE-style refinement | `design/goal-refinement.md` | Human validation of interpretation |
| Requirements (BRD/SRS) | `requirements/policy.json`, `requirements/traceability.csv` | Generator validates vocabulary |
| UML design | `design/domain.puml`, `design/sequence.puml` | Architectural review |
| ArchiMate mapping | `design/archimate-mapping.md` | Traceability review; not ArchiMate interchange |
| Formalization | `formal/DriverPass.lean` (generated) | Lean type checking |
| Axiomatization | Lean's built-in type theory; **no custom axioms** | Kernel check |
| Proof | `formal/Proofs.lean` (handwritten) | Lean checks four theorems |
| Scenario formal checking | `formal/Scenarios.lean` (generated) | Lean `decide` examples |
| Executable domain | `backend/src/domain.rs` (generated) | Rust unit/contract tests |
| API | `backend/src/main.rs`, `contracts/openapi.yaml` | HTTP smoke test |
| Persistence + audit | `backend/src/service.rs` (schema and transaction) | Unique constraint, smoke test, `backend/tests/transactions.rs` |
| Transaction model | `formal/Transactions.lean` (handwritten) | Lean proves atomicity, audit and no double booking, assuming SQLite rollback and `BEGIN IMMEDIATE` serialization |
| Build + deploy | `infra/Dockerfile`, `infra/compose.yaml` | OCI build |
| CI/CD | `.github/workflows/verify.yml` | Regenerate check → Lean proofs → Rust tests → HTTP → image |

## 4. Generate / verify the domain semantics

At the project root:

```bash
python3 scripts/generate.py
python3 scripts/generate.py --check
python3 scripts/check_contracts.py
```

To typecheck the generated Lean specification and its proofs (Lean installed by
`elan`, pinned in `lean-toolchain` to 4.35.0):

```bash
export LEAN_PATH=formal
lean -o formal/DriverPass.olean formal/DriverPass.lean
lean formal/Proofs.lean
lean formal/Scenarios.lean
lean formal/Transactions.lean
```

This project intentionally **does not require Mathlib**, so installation is
lighter. Once the minimal PoC is working, Mathlib may be useful for stronger
state-machine refinements, temporal assertions, separation logic, and
compositional arguments.

## 5. Compile, test, and run the Rust API

Install stable Rust and Cargo first. From the project root:

```bash
cargo test --manifest-path backend/Cargo.toml
cargo run --manifest-path backend/Cargo.toml
```

The server starts on **loopback** at `http://localhost:3000` (not a public network interface); instructor ID 7 is seeded.
For a clean trial, set a new file path: `DATABASE_PATH=/tmp/driverpass-demo.db`.

Open another terminal:

```bash
curl -s http://localhost:3000/api/v1/instructors/7
curl -i -X POST http://localhost:3000/api/v1/instructors/7/slots \
  -H 'Content-Type: application/json' -d '{"slot_id":42}'
curl -i -X POST http://localhost:3000/api/v1/instructors/7/slots \
  -H 'Content-Type: application/json' -d '{"slot_id":42}'
curl -i -X PATCH http://localhost:3000/api/v1/instructors/7/duty \
  -H 'Content-Type: application/json' -d '{"off_duty":true}'
curl -i -X POST http://localhost:3000/api/v1/instructors/7/slots \
  -H 'Content-Type: application/json' -d '{"slot_id":43}'
curl -s http://localhost:3000/api/v1/instructors/7
curl -s http://localhost:3000/api/v1/audit
```

Optional full HTTP/SQLite integration test against a **fresh temporary DB**:

```bash
cargo build --manifest-path backend/Cargo.toml
python3 scripts/smoke.py backend/target/debug/driverpass-poc
```

## 6. Run via container (locally bound only)

```bash
docker compose -f infra/compose.yaml up --build -d
curl http://localhost:3000/health
docker compose -f infra/compose.yaml down
```

SQLite data persists in a named Docker volume unless it is explicitly removed.
For the tutorial the host port is bound to `127.0.0.1` to avoid accidental
public exposure.

## 7. Change requirements and see the build gate

Try the following local experiment:

1. Edit `requirements/policy.json`, swapping the two guards. The generator
   deliberately rejects it: precedence needs semantic review. This is not
   a silent mutation of business logic.
2. Edit one of the **supported** scenario expectations in
   `contracts/scenarios.json`; regenerate. Lean's generated example or Rust's
   scenario test will fail if the expected behavior is inconsistent.
3. In `formal/Proofs.lean`, replace an expected property with a false property.
   Lean should reject the invalid proof claim.
4. Modify `backend/src/domain.rs` directly. `generate.py --check` fails,
   preventing divergent implementation from silently merging.

The design target is a **proof-carrying change workflow**, not a claim that
requirements automatically generate correct systems.

## 8. What's proved and what's still only tested?

**Proved when Lean checking succeeds:** Within the pure `Roster` transition,
(a) off-duty denial, (b) duplicate denial, (c) all rejected transitions preserve
state, (d) accepted transitions prepend the requested slot. No `sorry` or custom
axioms are used in these obligations.

**Tested, not mathematically proved:** Rust/Lean observational correspondence
(on shared examples and a bounded sweep); API semantics; SQLite transaction
behavior; HTTP responses; audit creation; compiled binary packaging.

**Neither modeled nor verified:** distributed concurrency, network failure,
crash-consistent message delivery, authentication/authorization, production
schema migrations, retry/idempotency semantics, cross-instructor collisions,
slot interval overlaps, compiler correctness, verified generation, and
complete end-to-end refinement proof. An initial unique DB constraint and
IMMEDIATE transaction help enforcement but are not substitutes for all these
proof obligations.

## 9. Suggested research-grade next iteration

Define a cross-language refinement/simulation relation with encoders for
`Roster` and `Decision`, prove equivalence for all valid input states, and
model the transactional database protocol as a state machine. Promote the
semantic generator from a fixed vocabulary to a typed intermediate
representation for business goals, constraints, state transitions, and
invariants. Export typed generated artifacts for UML/ArchiMate views,
OpenAPI schemas, Lean specs, Rust implementation, and TLA+/Apalache or
Alloy bounded concurrency checks. Require semantic trace links and proof
certificates on every CI build.

The claim of this PoC is deliberately modest: it is an **inspectable,
reproducible requirement-to-runtime pathway** with several real proof
obligations, not a verified enterprise system.
