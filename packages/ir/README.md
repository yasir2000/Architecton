# Typed artifact IR (v1)

The first package of the [research roadmap](../../README.md#research-roadmap-next-work-packages): a typed intermediate representation (IR) that records, in one checked file, what a system is meant to do and where each claim lives.

An IR file holds:

| Element | Holds | Checked |
|---|---|---|
| **Artifacts** | path and SHA-256 of each source, design, proof, code and test file | file exists; hash matches the reviewed one |
| **Goals** | stakeholder goals and their refinement tree | parents exist; no cycles |
| **Requirements** | business, system and nonfunctional statements | each refines at least one goal |
| **Risks** | identified risks, status (`mitigated`, `accepted`, `open`) and mitigating requirements | mitigations exist; a `mitigated` risk names at least one |
| **State variables** | typed state (`Bool`, `Nat`, `List Nat`) | names distinct |
| **Transitions** | typed parameters, ordered guards, an `otherwise` effect | guards are Boolean; effects match the type of the variable they write |
| **Invariants** | state predicates | Boolean; may not mention parameters |
| **Provenance anchors** | on every goal, requirement and risk: artifact, anchor text, role (`source`, `design`, `proof`, `implementation`, `test`) | artifact declared; anchor text really occurs in it, including inside `.docx` files |

The first instance is [examples/driverpass/ir/driverpass.ir.json](../../examples/driverpass/ir/driverpass.ir.json). It ties the DriverPass BRD, policy, goal refinement, UML, Lean proofs, Rust code and tests together.

## Two independent checks

```text
driverpass.ir.json ──► irc.py check ──► structure, types, references, cycles,
        │                               artifact hashes, anchor text
        └────────────► irc.py lean ───► DriverPassIR.lean (generated)
                                              │ import ArtifactIR
                                              ▼
                                Lean kernel: wellFormed driverPass = true
```

- [scripts/irc.py](scripts/irc.py), the checker and generator. It uses only the Python standard library. Its vocabulary is closed: unknown keys, types, operators, kinds, statuses or roles are errors.
- [formal/ArtifactIR.lean](formal/ArtifactIR.lean), the reference semantics. It defines the expression language, its type checker `typeOf`, its evaluator `eval` and the whole-model check `wellFormed`, and proves:
  - `eval_sound`: a well-typed expression, evaluated in an environment that matches its declared types, always produces a value of its type, so it never gets stuck;
  - `wf_guard_evaluates`, `wf_effect_type_preserving`, `wf_invariant_evaluates`: in a well-formed model, every guard is a Boolean, every effect writes a value of the right type, and every invariant is a Boolean predicate on state;
  - `wf_requirement_traced`: every requirement refines a declared goal.
- [formal/Step.lean](formal/Step.lean), the operational semantics of transitions. Guards fire in order; if none fires, all effects are evaluated in the pre-state and written together. For every well-formed model it proves:
  - `step_progress`: a transition never gets stuck on inputs that match the declared types;
  - `step_preserves_conforms`: the new state still matches the declared state types.
- [formal/Negative.lean](formal/Negative.lean) has kernel-checked proofs that `wellFormed` **rejects** nine kinds of broken models. [tests/test_irc.py](tests/test_irc.py) has 38 Python tests. Most break the real DriverPass IR in one specific way; the rest test the Python interpreter.

The structural and typing rules are checked twice, by Python and by the Lean kernel, so a bug in one checker alone can't pass a malformed IR. Hashes and anchor text are checked by Python only.

## Cross-language conformance (DriverPass)

```text
                 ir_refines_allocate (Lean, all inputs)
  IR transition ◄────────────────────────────────────► Lean allocate
       │                                                    ▲
       │ gen_oracle.py (Python interpreter, untrusted)      │ oracle_matches_allocate
       ▼                                                    │ (Lean kernel, 850 vectors)
  ir/oracle.json ───────────────────────────────────────────┘
       │
       └──► backend/tests/oracle.rs ──► Rust allocate (same 850 vectors)
```

- [Refinement.lean](../../examples/driverpass/ir/Refinement.lean) proves that the IR transition `TR-assign_slot` computes exactly `DriverPass.allocate` for **every** roster and slot, and that both preserve invariant INV-001.
- [gen_oracle.py](../../examples/driverpass/scripts/gen_oracle.py) enumerates a bounded domain (every roster of length ≤ 3 over slots 0–3, duplicates included, both duty states, requests 0–4) and computes the expected results with the Python interpreter.
- [Oracle.lean](../../examples/driverpass/ir/Oracle.lean) has the Lean kernel re-check all 850 vectors against `allocate`, so a bug in the Python interpreter can't produce a wrong oracle. [oracle.rs](../../examples/driverpass/backend/tests/oracle.rs) replays them against the Rust `allocate`.

Result: the IR and Lean agree for all inputs; Rust agrees with both on the 850 vectors. Agreement for **all** Rust inputs is not proved, and Rust's `i64` slots include negative values that Lean's `Nat` cannot represent. The API rejects negative slots before calling `allocate`.

## What this does not establish

- **Faithfulness.** Whether the IR correctly captures the natural-language requirements is a human review decision. The anchors show *where* a claim comes from, not that it was interpreted correctly.
- **Realization, in general.** An `implementation` or `proof` anchor shows that the named function or theorem exists in the pinned file, not that it implements or proves the requirement. For DriverPass's `assign_slot`, the conformance chain above closes this gap: fully for Lean, and on the bounded oracle for Rust. Other anchors, such as SR-002's transaction code, are still existence-only.
- **Evidence strength.** A `test` anchor only says a test touches the requirement. For example, `scripts/smoke.py` sends requests one at a time, so on its own it does not test SR-002's atomicity under concurrency; `backend/tests/transactions.rs`, also anchored on SR-002, does.
- **Trust in the hashes.** Hashes detect drift after review; they are not signed. Signed attestations belong to the trusted evidence ledger work package.

## Run checks

From the repository root:

```bash
python3 -m unittest discover -s packages/ir/tests -v
python3 packages/ir/scripts/irc.py check examples/driverpass/ir/driverpass.ir.json
python3 packages/ir/scripts/irc.py lean --check examples/driverpass/ir/driverpass.ir.json \
    --out examples/driverpass/ir/DriverPassIR.lean --ident driverPass
python3 examples/driverpass/scripts/gen_oracle.py --check
cargo test --manifest-path examples/driverpass/backend/Cargo.toml --test oracle

# Requires Lean 4.35.0 (pinned in packages/ir/lean-toolchain).
# LEAN_PATH separates entries with ':' on Linux/macOS and ';' on Windows.
cd packages/ir
DP=../../examples/driverpass
export LEAN_PATH="formal:$DP/formal:$DP/ir"
lean -o formal/ArtifactIR.olean formal/ArtifactIR.lean
lean -o formal/Step.olean formal/Step.lean
lean formal/Negative.lean
lean -o $DP/formal/DriverPass.olean $DP/formal/DriverPass.lean
lean -o $DP/ir/DriverPassIR.olean $DP/ir/DriverPassIR.lean
lean $DP/ir/Refinement.lean
lean $DP/ir/Oracle.lean
```

After an IR change, regenerate the oracle with `python3 examples/driverpass/scripts/gen_oracle.py --write`.

## When an artifact changes

Any edit to a pinned artifact, such as `policy.json` or `domain.rs`, makes `irc.py check` fail with "changed since review". This is intended: someone must re-read the change, update the IR if its meaning changed, and then re-pin:

```bash
python3 packages/ir/scripts/irc.py hash --update examples/driverpass/ir/driverpass.ir.json
python3 packages/ir/scripts/irc.py lean --write examples/driverpass/ir/driverpass.ir.json \
    --out examples/driverpass/ir/DriverPassIR.lean --ident driverPass
```

Text files are hashed with LF line endings, so Windows and Linux checkouts agree. Binary files are hashed as they are.
