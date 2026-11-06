# Temporal core

Linear temporal logic (LTL) for Architecton, in plain Lean 4 with no Mathlib. Properties of *whole runs* of the lifecycle and DriverPass models (safety, deadlock-freedom, liveness under fairness, response), kernel-checked.

This is sub-project 1 of the temporal/runtime verification work package. Design: [spec](../../docs/superpowers/specs/2026-11-06-temporal-core-design.md).

## What is here

| File | Contents |
|---|---|
| `formal/Temporal.lean` | `LTL α` syntax; `sat` over infinite traces `Nat → α`; `satF` over finite traces `List α` (LTLf: strong `next` is false at the last position, weak `wnext` is true) |
| `formal/Bridge.lean` | `safe_prefix`: a safety formula true on an infinite trace is true on every non-empty prefix, so a finite log that violates it is a real violation. `cosafe_prefix`: a finite witness proves an eventuality. Characterisation lemmas for both semantics |
| `formal/System.lean` | step-function systems, record traces `⟨pre, input, post, out⟩`, invariant/step/ranking proof rules, weak and strong fairness |
| `formal/LifecycleTemporal.lean` | L1–L6 for `packages/lifecycle/formal` (imported unchanged) |
| `formal/DriverPassTemporal.lean` | D1–D5 for `examples/driverpass/formal/Transactions.lean` (imported unchanged) |
| `formal/Examples.lean` | `decide`-checked traces, non-vacuity runs, `#print axioms` for every main theorem |
| `scripts/verify.py` | builds everything in order and runs the axiom audit |
| `scripts/check_axioms.py` | fails on `sorry`, `axiom` declarations, `native_decide`, or axioms other than `propext`, `Quot.sound`, `Classical.choice` |

## Properties

Every theorem holds for **every input stream**, unless assumptions are listed.

### Lifecycle

| Id | Kind | Statement | Assumptions |
|---|---|---|---|
| L1 | safety | an accepted promotion had its gate satisfied and moved to the direct successor phase | none |
| L2 | safety | a requirements revision clears evidence, returns to inception and archives the old baseline | none |
| L3 | safety | the phase stays, advances one step, or returns to inception | none |
| L4 | safety | evidence is only lost on a requirements revision | none |
| L5 | deadlock-freedom | `iterate` is always accepted; from *any* state, `reachCmds` reaches `transition` | none |
| L6 | liveness | `transition` is eventually reached | requirements eventually stop changing; every gate evidence item is recorded infinitely often; promotion is attempted infinitely often |

Each L6 assumption is necessary: `L6_needs_no_revise`, `L6_needs_evidence` and `L6_needs_promote` give a stream that meets the other two and never reaches `transition`. `L6_ltl` states L6 as a single LTL formula `assumptions → ◇ transition`.

### DriverPass

| Id | Kind | Statement | Assumptions |
|---|---|---|---|
| D1 | safety | no instructor is ever double-booked | the initial database has no double booking |
| D2 | safety | an undecided request changes nothing; allocations only grow | none |
| D3 | response | a fault-free request for a known instructor is decided and audited exactly once, in the same step | none |
| D4a | progress | an on-duty instructor's fault-free request for a free slot is accepted | none |
| D4b | liveness | the slot is eventually booked and stays booked, despite arbitrary faults before and after | the instructor is on duty; **one** fault-free request for the slot is made (`D4b_once`). The spec's form, assuming the client retries infinitely often (`D4b`), is a corollary: retrying is not what makes it hold |
| D5 | violation | the lost-update interleaving violates `□ allocOkB` on a two-state trace, so (by `safe_prefix`) on every continuation | none |

## Run the checks

From the repository root (`python3` on Linux/macOS):

```bash
python -m unittest discover -s packages/temporal/tests -v
python packages/temporal/scripts/verify.py
```

`verify.py` ends with `axioms ok (19 theorems)` on success. CI: [verify-temporal.yml](../../.github/workflows/verify-temporal.yml). Evidence-ledger check: `temporal-lean`.

## Assurance boundary

- The theorems are about the **Lean models**, not the running Rust service or a deployed system. They inherit DriverPass assumptions A1 (atomicity) and A2 (isolation, serial order) from `Transactions.lean` and the lifecycle's trusted-attestation assumption.
- Fairness conditions are assumptions about the environment (clients retry; the team keeps recording evidence and promoting). The system does not guarantee them.
- Runtime trace monitoring, concurrency beyond A2, and distributed consistency are out of scope here and belong to later sub-projects.
