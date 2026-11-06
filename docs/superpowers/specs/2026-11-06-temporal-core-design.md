# Lean temporal core: design

- **Date:** 2026-11-06
- **Status:** approved design, awaiting implementation plan
- **Backlog item:** Temporal/runtime verification (README research roadmap), sub-project 1 of 4
- **Package:** `packages/temporal/`

## 1. Purpose and scope

Architecton's evidence so far is about single steps: each transition of the DriverPass and lifecycle models is proved correct. This sub-project extends the evidence to **behaviour over time**: properties of whole runs (safety, deadlock-freedom, liveness under fairness, response), stated in linear temporal logic (LTL) and proved by the Lean kernel.

The temporal/runtime backlog item is split into four sub-projects, each with its own spec:

1. **Lean temporal core** (this spec).
2. Runtime trace monitor: check the Rust service's `allocation_audit` log against formulas from this core.
3. TLA+ concurrency model of concurrent requests and SQLite transactions.
4. Distributed consistency.

### Success criteria

- One LTL syntax with an infinite-trace semantics and a finite-trace (LTLf) semantics, and proved theorems that link them.
- The lifecycle properties L1–L6 and DriverPass properties D1–D5 (section 5), proved with no `sorry`, no project axioms, and only Lean's standard axioms.
- Existing model files are imported, not edited.
- Checked in CI on every change to the temporal package or to either model, and registered in the evidence ledger.

### Non-goals

No CTL or branching time, no automata construction or model checker, no parser for textual formulas, no real-time or metric operators, no Mathlib.

## 2. Package layout

```
packages/temporal/
  README.md
  lean-toolchain            leanprover/lean4:v4.35.0 (same as other packages)
  formal/
    Temporal.lean           LTL syntax, infinite and finite semantics
    Bridge.lean             theorems linking the two semantics; dualities
    System.lean             step-function systems, runs, proof rules, fairness
    LifecycleTemporal.lean  L1–L6 (imports packages/lifecycle/formal)
    DriverPassTemporal.lean D1–D5 (imports examples/driverpass/formal)
    Examples.lean           decide-checked traces, sanity runs, #print axioms
  scripts/
    check_axioms.py         fails on sorry, project axioms or non-standard axioms
```

Plain Lean 4 core, consistent with the rest of the repository.

## 3. Core semantics (`Temporal.lean`)

**Formulas.** `inductive LTL (α : Type)`:

| Constructor | Meaning |
|---|---|
| `tt` | true |
| `atom (p : α → Bool)` | holds at a position when `p` holds of its element |
| `not φ`, `and φ ψ`, `or φ ψ` | Boolean connectives |
| `next φ` | strong next |
| `until φ ψ` | strong until |

Derived: `ff`, `imp`, `eventually` (◇), `always` (□), `wnext` (◯̃, weak next, `¬◯¬`), `wuntil` (W, `φ U ψ ∨ □φ`). Atoms are Boolean so the finite evaluator is decidable.

**Infinite semantics.** `sat (w : Nat → α) (i : Nat) : LTL α → Prop`, standard LTL. `next φ` holds at `i` iff `φ` holds at `i+1`; `until φ ψ` holds at `i` iff some `k ≥ i` satisfies `ψ` and every `j` with `i ≤ j < k` satisfies `φ`.

**Finite semantics (LTLf).** `satF (w : List α) (i : Nat) : LTL α → Bool`, total and structurally recursive, so `decide` and `#eval` work. Positions `i ≥ w.length` are outside the trace; there, atoms are false. `next φ` at the last position is **false** (strong next); `wnext φ` there is **true**. `until` searches positions `i … w.length - 1`.

## 4. Linking the semantics, proof rules and fairness

### 4.1 Bridge theorems (`Bridge.lean`)

- `Safe φ`: a syntactic predicate on formulas built from atoms, negated atoms, `and`, `or`, `wnext`, `always` and `wuntil` (no `until`, `eventually` or strong `next`).
- **`safe_prefix`**: `Safe φ → sat w 0 φ → ∀ n ≥ 1, satF (prefix w n) 0 φ = true`, where `prefix w n` is the list of the first `n` elements `w 0` to `w (n-1)`. The empty prefix is excluded because LTLf makes atoms false on an empty trace.
  Contrapositive, which is the form a monitor uses: a finite log that violates a safe formula is violated by every infinite extension of it.
- `CoSafe φ`: atoms, negated atoms, `and`, `or`, `next`, `until`, `eventually` (no `always`, `wnext` or `wuntil`).
- **`cosafe_prefix`**: `CoSafe φ → satF (prefix w n) 0 φ = true → sat w 0 φ`. A finite witness proves an eventuality.
- Sanity lemmas: `satF_always_atom` (`□ atom p` on a list ⇔ `∀ x ∈ w, p x`); dualities `¬◇¬φ ≡ □φ`, `φ W ψ ≡ φ U ψ ∨ □φ`, holding in both semantics where they apply.

### 4.2 Systems and runs (`System.lean`)

```lean
structure System (σ ι ο : Type) where
  init : σ
  step : σ → ι → σ × ο

structure Rec (σ ι ο : Type) where
  pre : σ
  input : ι
  post : σ
  out : ο
```

- `states sys u : Nat → σ` (state before step `n`) for an input stream `u : Nat → ι`.
- `run sys u : Nat → Rec σ ι ο`: record `n` is `⟨states n, u n, (step (states n) (u n)).1, (step …).2⟩`.
- `runF sys us : List (Rec σ ι ο)` for a finite input list; `runF sys (take n u) = prefix (run sys u) n` is proved.
- `runFrom sys s u`: the same with an arbitrary start state, for properties that hold from any state.

Trace elements are transition records, so formulas can refer to inputs and outputs (“promote was accepted”), not only states.

### 4.3 Proof rules

Used by the instance files so that they do not unfold `sat` directly.

- **Invariant rule.** `P sys.init` and `∀ s i, P s → P (sys.step s i).1` give `sat (run sys u) 0 (□ atom (P ∘ Rec.post))` and the same for `pre`, for every `u`.
- **Step rule.** `∀ s i, Q s i (sys.step s i)` gives `□ atom Q'` on the record trace, where `Q'` reads `Q` from a record.
- **Ranking rule.** For `μ : σ → Nat` with `μ (step s i).1 ≤ μ s` for all steps from some position on, strict decrease on steps satisfying a predicate `helpful`, `helpful` steps infinitely often while `μ > 0` and `goal` whenever `μ = 0`: `sat run 0 (◇ goal)`.

### 4.4 Fairness

The models are driven by their inputs, so fairness is stated as assumptions on the input stream, as LTL formulas over the record trace:

- `infOften p := □◇ p`
- `WF enabled taken := ◇□ enabled → □◇ taken`
- `SF enabled taken := □◇ enabled → □◇ taken`

Every liveness theorem has the form `sat (run sys u) 0 (assumptions → ◇ goal)`, so its dependencies are explicit.

## 5. Properties

All theorems quantify over every input stream unless assumptions are listed.

### 5.1 Lifecycle (`LifecycleTemporal.lean`)

System: `Lifecycle.step` from `Lifecycle.initial`; input `Command`, output `Outcome`.

| Id | Kind | Statement |
|---|---|---|
| L1 | safety | `□(input = promote ∧ out = accepted → Gate pre ∧ nextPhase pre.phase = some post.phase)` |
| L2 | safety | `□(input = reviseRequirements → post.verified = [] ∧ post.phase = inception ∧ (pre.revision, pre.verified) ∈ post.archive)` |
| L3 | safety | `□(post.phase = pre.phase ∨ nextPhase pre.phase = some post.phase ∨ post.phase = inception)` |
| L4 | safety | `□(input ≠ reviseRequirements → ∀ e ∈ pre.verified, e ∈ post.verified)` |
| L5 | deadlock-freedom | `iterate` is accepted in every state; from every state there is an explicit finite input list whose final state has `phase = transition` |
| L6 | liveness | `◇□ ¬revise ∧ (∀ e ∈ gateEvidence, □◇ recordValidated e) ∧ □◇ promote → ◇(phase = transition)` |

`gateEvidence` lists the evidence items required by the generated gate (`Policy.lean`) for inception, elaboration and construction.

**L6 necessity.** For each of the three assumptions, an explicit periodic input stream satisfies the other two and never reaches `transition` (for example: revise on every other step; never promote; never record `artifactBuilt`). Each is a proved theorem.

### 5.2 DriverPass (`DriverPassTemporal.lean`)

System: `assignTx` over `Db`; input `(i, slot, fault) : Nat × Nat × Option Fault`; output `Response`; initial state any `db` with `NoDoubleBooking db` (a parameter of the theorems).

| Id | Kind | Statement |
|---|---|---|
| D1 | safety | `□ allocOkB post` on every run, with `allocOkB` a Boolean form of `AllocOk`, proved equivalent |
| D2 | safety | `□(out is not decided → post = pre)` and `□(∀ a ∈ pre.allocations, a ∈ post.allocations)` |
| D3 | response | `□(roster pre i ≠ none ∧ fault = none → ∃ d r, out = decided d r ∧ post.audit = (i, slot, d) :: pre.audit)` |
| D4a | progress | for every db, if `roster db i = some r` with `r.offDuty = false` and `slot ∉ slotsOf db.allocations i`, then input `(i, slot, none)` returns `decided accepted` |
| D4b | liveness | `roster db i = some r` with `r.offDuty = false` for the initial db ∧ `□◇(input = (i, slot, none))` → `◇□(slot ∈ slotsOf post.allocations i)` |
| D5 | violation | `racyTrace : List Db` is `[demo, racyPair demo 7 42]` (the state before and after the lost-update interleaving); `satF racyTrace 0 (□ atom allocOkB) = false` by `decide`, so by `safe_prefix` every infinite state sequence starting with this trace violates `□ atom allocOkB` |

D4b holds with arbitrary faults in between because `assignTx` never changes `instructors` and allocations only grow (D2).

## 6. Build, CI and evidence

- **Build:** `packages/ledger/scripts/lean_build.py` with `--path` for `packages/lifecycle/formal`, `examples/driverpass/formal` and `packages/temporal/formal`. Order: the lifecycle modules (`ArchitectonLifecycle`, `Policy`, `StateMachine`), the DriverPass modules (`DriverPass`, `Transactions`), then `Temporal`, `Bridge`, `System`, `LifecycleTemporal`, `DriverPassTemporal`, `Examples`.
- **CI:** new `.github/workflows/verify-temporal.yml`, triggered by changes under `packages/temporal/**`, `packages/lifecycle/formal/**`, `examples/driverpass/formal/**` or the workflow itself. It runs the build, then `check_axioms.py`.
- **Axiom audit:** `Examples.lean` ends with `#print axioms` for L1–L6, D1–D5, `safe_prefix` and `cosafe_prefix`. `check_axioms.py` fails on any `sorry`, any `axiom` declaration in the package, or any axiom other than `propext`, `Quot.sound` and `Classical.choice`.
- **Evidence ledger:** add check `temporal-lean` to `evidence/checks.json`. Inputs: `packages/temporal/formal/*.lean`, `packages/temporal/scripts/*.py`, `packages/lifecycle/formal/*.lean`, `examples/driverpass/formal/*.lean`. A change to either model then revokes the temporal evidence.

## 7. Testing

- `Examples.lean`: `decide`-checked `satF` results on hand-written traces, with a passing and a failing case for each operator, the strong/weak next difference at the last position, and D5.
- Non-vacuity: each of L1–L6 and D1–D5 has one concrete run on which its antecedent actually occurs. L6 and D4b additionally have a concrete periodic input stream proved to satisfy all their assumptions.

## 8. Documentation

- `packages/temporal/README.md`: purpose, the L/D property table with exact assumptions, build commands, assurance boundary.
- `README.md` roadmap and `packages/README.md`: temporal/runtime verification becomes “partially implemented (Lean temporal core)”.
- `docs/assurance.md`: the boundary below.
- `CHANGELOG.md`: an entry under Unreleased.

## 9. Assurance boundary

- The theorems are about the **Lean models**, not the running Rust service or a deployed system. They inherit DriverPass assumptions A1 (atomicity) and A2 (isolation, serial order) from `Transactions.lean` and the lifecycle's trusted-attestation assumption.
- Fairness conditions are assumptions about the environment (clients retry; the team keeps recording evidence and promoting). The system does not guarantee them.
- Runtime trace monitoring, concurrency beyond A2, and distributed consistency are out of scope and belong to sub-projects 2–4.
