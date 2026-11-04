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
- [formal/Negative.lean](formal/Negative.lean) has kernel-checked proofs that `wellFormed` **rejects** nine kinds of broken models. [tests/test_irc.py](tests/test_irc.py) has 31 Python tests, most of which break the real DriverPass IR in one specific way.

The structural and typing rules are checked twice, by Python and by the Lean kernel, so a bug in one checker alone can't pass a malformed IR. Hashes and anchor text are checked by Python only.

## What this does not establish

- **Faithfulness.** Whether the IR correctly captures the natural-language requirements is a human review decision. The anchors show *where* a claim comes from, not that it was interpreted correctly.
- **Realization.** An `implementation` or `proof` anchor shows that the named function or theorem exists in the pinned file. It does not show that it implements or proves the requirement. Linking IR transitions to `DriverPass.allocate` and the Rust code is the next work package (cross-language conformance).
- **Evidence strength.** A `test` anchor only says a test touches the requirement. For example, `scripts/smoke.py` sends requests one at a time, so it does not test SR-002's atomicity under concurrency.
- **Trust in the hashes.** Hashes detect drift after review; they are not signed. Signed attestations belong to the trusted evidence ledger work package.

## Run checks

From the repository root:

```bash
python3 -m unittest discover -s packages/ir/tests -v
python3 packages/ir/scripts/irc.py check examples/driverpass/ir/driverpass.ir.json
python3 packages/ir/scripts/irc.py lean --check examples/driverpass/ir/driverpass.ir.json \
    --out examples/driverpass/ir/DriverPassIR.lean --ident driverPass

# Requires Lean 4.35.0 (pinned in packages/ir/lean-toolchain):
cd packages/ir
LEAN_PATH=formal lean -o formal/ArtifactIR.olean formal/ArtifactIR.lean
LEAN_PATH=formal lean formal/Negative.lean
LEAN_PATH=formal lean ../../examples/driverpass/ir/DriverPassIR.lean
```

## When an artifact changes

Any edit to a pinned artifact, such as `policy.json` or `domain.rs`, makes `irc.py check` fail with "changed since review". This is intended: someone must re-read the change, update the IR if its meaning changed, and then re-pin:

```bash
python3 packages/ir/scripts/irc.py hash --update examples/driverpass/ir/driverpass.ir.json
python3 packages/ir/scripts/irc.py lean --write examples/driverpass/ir/driverpass.ir.json \
    --out examples/driverpass/ir/DriverPassIR.lean --ident driverPass
```

Text files are hashed with LF line endings, so Windows and Linux checkouts agree. Binary files are hashed as they are.
