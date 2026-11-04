# Goal-to-design semantic refinement

## Stakeholder intention (natural language, not automatically proved)

**G0:** An instructor must never acquire an invalid lesson allocation.

### Refinement / assumptions

- G1 (BR-001): If off-duty at the instant of assignment, reject it.
- G2 (BR-002): If the *same instructor* already holds the slot, reject it.
- G3 (BR-003): Otherwise assign the slot exactly once.
- G4 (SR-001): All rejection outcomes leave the roster unchanged.
- G5 (SR-002): Read/decide/write must be an atomic SQLite transaction.
- G6 (SR-003): Every processed attempt for a known instructor must produce a durable audit record.

**Deliberate scope:** This PoC only prevents *per-instructor* duplicate slot IDs. It does
not model an organization-wide resource conflict, driving-test capacity, geographic
travel time, time-zone rules, or overlapping slot intervals. Slot ID is treated as an
opaque nonnegative identifier, not a timestamp.

## Semantic chain

1. Analyst states intention and acceptance criteria in ordinary language.
2. Engineer normalizes one operation to ordered guards and an effect, in
   `requirements/policy.json`. This is the **human semantic validation point**.
3. `scripts/generate.py` maps the small supported guard vocabulary to a pure Lean
   `allocate` definition and a pure Rust `allocate` function.
4. Independently handwritten Lean theorems in `formal/Proofs.lean` state the intended
   safety properties of the generated function. A failed theorem blocks CI.
5. Shared scenarios generate additional kernel-checked examples in Lean, and are read
   as test data by Rust's domain tests.
6. Axum wraps the Rust function with a SQLite transaction and persistent audit.
7. HTTP smoke testing checks the behavior through the deployed application's
   observable interface. This does **not** prove all possible runtime behaviors.

## Correctness statement and assurance limit

The intended simulation relation between implementations is:

```
encode( Lean.allocate(decode(rustRoster), slot) )
    == Rust.allocate(rustRoster, slot)
```

for valid, nonnegative `i64` slot identifiers and rosters. The PoC verifies a finite
set of scenarios and a bounded Rust sweep. It does **not** prove the above relation
for every input, nor verify the generator, compiler, database engine, Axum, hardware,
network, audit durability under power loss, or distributed deployment semantics.

Formal proofs establish properties **of the Lean model** under its assumptions.
A separate verified refinement or proof-producing code generator would be needed
for an end-to-end mathematical guarantee about production binaries.
