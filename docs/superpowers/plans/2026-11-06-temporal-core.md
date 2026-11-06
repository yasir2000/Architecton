# Lean Temporal Core Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `packages/temporal/`: an LTL library in plain Lean 4 with infinite and finite semantics, bridge theorems, proof rules, and kernel-checked temporal properties L1–L6 (lifecycle) and D1–D5 (DriverPass).

**Architecture:** Deep embedding `LTL α` with two evaluators (`sat` over `Nat → α`, `satF` over `List α`). `System.lean` turns the existing step functions into record traces `Rec = ⟨pre, input, post, out⟩` and provides invariant, step and ranking proof rules. Instance files import the existing lifecycle and DriverPass modules unchanged. `scripts/verify.py` builds everything with `lean_build.py` and audits axioms; CI and the evidence ledger call it.

**Tech Stack:** Lean 4 v4.35.0 core (no Mathlib), Python 3 (stdlib `unittest`), GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-11-06-temporal-core-design.md`

## Global Constraints

- Lean toolchain `leanprover/lean4:v4.35.0`; plain Lean 4 core, **no Mathlib**.
- No `sorry`, no `axiom` declarations, no `native_decide`; only axioms `propext`, `Quot.sound`, `Classical.choice` may appear in `#print axioms`.
- Do **not** edit anything under `packages/lifecycle/formal/` or `examples/driverpass/formal/`; import them.
- All Lean code in `namespace Architecton.Temporal` (instance files may `open Architecton.Lifecycle` / `DriverPassTx`).
- `satF` and all its helpers use **structural recursion only** (no `termination_by`/well-founded recursion), so `decide` can reduce them in the kernel.
- Commits: `git commit -s` (DCO sign-off); no Claude/AI co-author trailer.
- Python: invoke as `python` on Windows, `python3` on Linux/CI; scripts must work with either.
- **Build command** (referred to below as `BUILD <files>`), run from the repo root:
  `python packages/ledger/scripts/lean_build.py --path packages/lifecycle/formal --path examples/driverpass/formal --path packages/temporal/formal <files>`
  Dependency prefix used by every task (call it `DEPS`): `packages/lifecycle/formal/ArchitectonLifecycle.lean packages/lifecycle/formal/Policy.lean packages/lifecycle/formal/StateMachine.lean examples/driverpass/formal/DriverPass.lean examples/driverpass/formal/Transactions.lean`
  Each `BUILD` prints `ok   <file>` per file and exits 0 on success, `FAIL <file>` and non-zero otherwise.

## Review Focus

1. **`decide` on `satF` not reducing** (an evaluator written with well-founded recursion makes `by decide` fail or hang). Pinned by the operator tests in Task 1, which must pass by `decide`.
2. **Out-of-range positions and the empty trace** (atoms false, `next` false, `wnext` true, `always` vacuously true past the end). Pinned by Task 1 edge-case examples and Task 2's `i < n` hypotheses.
3. **`#print axioms` output wrapped over several lines** for long axiom lists, or a theorem silently missing from the audit. Pinned by Task 8 parser tests (multi-line case, missing-theorem case).
4. **Windows path separators in `LEAN_PATH`** and `python` vs `python3`. Pinned by running `verify.py` locally on Windows in Task 8 and on Linux in CI (Task 9).
5. **Vacuous theorems** (assumptions that can never hold). Pinned by the non-vacuity examples in Tasks 4–7.

---

### Task 1: Package scaffold, LTL syntax and both semantics

**Files:**
- Create: `packages/temporal/lean-toolchain` (content `leanprover/lean4:v4.35.0`)
- Create: `packages/temporal/formal/Temporal.lean`
- Create: `packages/temporal/formal/Examples.lean`

**Interfaces:**
- Produces:
  - `inductive LTL (α : Type) | tt | atom (p : α → Bool) | not (φ : LTL α) | and (φ ψ : LTL α) | or (φ ψ : LTL α) | next (φ : LTL α) | until (φ ψ : LTL α)`
  - derived `def`s: `LTL.ff := not tt`, `LTL.imp φ ψ := or (not φ) ψ`, `LTL.eventually φ := until tt φ`, `LTL.always φ := not (eventually (not φ))`, `LTL.wnext φ := not (next (not φ))`, `LTL.wuntil φ ψ := or (until φ ψ) (always φ)`, `LTL.all : List (LTL α) → LTL α` (fold with `and`, `[] ↦ tt`)
  - `def sat (w : Nat → α) : Nat → LTL α → Prop` (standard LTL; `until`: `∃ k ≥ i, sat w k ψ ∧ ∀ j, i ≤ j → j < k → sat w j φ`)
  - `def satF (w : List α) : Nat → LTL α → Bool` (atom at `i ≥ w.length` is `false`; `next φ` at `i` is `decide (i+1 < w.length) && satF w (i+1) φ`; `until` scans `i … w.length-1` via a structurally recursive helper on fuel `w.length - i`)

- [ ] **Step 1: Write the failing examples** in `Examples.lean` (`import Temporal`, `open Architecton.Temporal`), each `:= by decide`:

```lean
example : satF [1,2,3] 0 (.always (.atom (· > 0))) = true := by decide
example : satF [1,2,3] 0 (.always (.atom (· > 1))) = false := by decide
example : satF [1,2,3] 0 (.eventually (.atom (· = 3))) = true := by decide
example : satF [1,2,3] 0 (.eventually (.atom (· = 4))) = false := by decide
example : satF [1,1,2] 0 (.until (.atom (· = 1)) (.atom (· = 2))) = true := by decide
example : satF [1,3,2] 0 (.until (.atom (· = 1)) (.atom (· = 2))) = false := by decide
example : satF [1] 0 (.next .tt) = false := by decide      -- strong next at the end
example : satF [1] 0 (.wnext .ff) = true := by decide      -- weak next at the end
example : satF ([] : List Nat) 0 (.atom (fun _ => true)) = false := by decide
example : satF ([] : List Nat) 0 (.always (.atom (fun _ => false))) = true := by decide
example : satF [1,2] 0 (.wuntil (.atom (· < 5)) (.atom (· = 9))) = true := by decide
```

- [ ] **Step 2: Run to verify failure.** `BUILD DEPS packages/temporal/formal/Examples.lean` → `FAIL` (unknown module `Temporal`).
- [ ] **Step 3: Implement `Temporal.lean`** with the interfaces above. Module doc comment: what the two semantics are and the LTLf conventions.
- [ ] **Step 4: Run.** `BUILD DEPS packages/temporal/formal/Temporal.lean packages/temporal/formal/Examples.lean` → all `ok`.
- [ ] **Step 5: Commit.** `git add packages/temporal && git commit -s -m "feat(temporal): add LTL syntax with infinite and finite semantics"`

### Task 2: Bridge theorems (`Bridge.lean`)

**Files:**
- Create: `packages/temporal/formal/Bridge.lean`
- Modify: `packages/temporal/formal/Examples.lean` (import `Bridge`, add uses)

**Interfaces:**
- Consumes: Task 1.
- Produces:
  - `def prefix (w : Nat → α) (n : Nat) : List α := (List.range n).map w`; `theorem prefix_length : (prefix w n).length = n`; `theorem prefix_get (h : i < n) : (prefix w n)[i] = w i` (any equivalent indexing form)
  - `inductive Safe : LTL α → Prop` with constructors for `tt`, `atom p`, `not (atom p)`, `and`, `or`, `wnext`, `always`, `wuntil` (the last three on the derived forms)
  - `inductive CoSafe : LTL α → Prop` with `tt`, `atom p`, `not (atom p)`, `and`, `or`, `next`, `until`, `eventually`
  - `theorem safe_prefix_at (hφ : Safe φ) (h : sat w i φ) (hn : i < n) : satF (prefix w n) i φ = true`
  - `theorem safe_prefix (hφ : Safe φ) (h : sat w 0 φ) (hn : 1 ≤ n) : satF (prefix w n) 0 φ = true`
  - `theorem cosafe_prefix_at (hφ : CoSafe φ) (hn : i < n) (h : satF (prefix w n) i φ = true) : sat w i φ`; `theorem cosafe_prefix` (the `i = 0` form)
  - Characterisation lemmas used by later tasks: `sat_always_iff : sat w i (.always φ) ↔ ∀ j ≥ i, sat w j φ`; `sat_eventually_iff : sat w i (.eventually φ) ↔ ∃ j ≥ i, sat w j φ`; `sat_atom_iff : sat w i (.atom p) ↔ p (w i) = true`; `sat_imp_iff`; `sat_and_iff`; `sat_wnext_iff : sat w i (.wnext φ) ↔ sat w (i+1) φ`; `satF_always_atom : satF w 0 (.always (.atom p)) = w.all p`; duality `sat_not_eventually_not : sat w i (.not (.eventually (.not φ))) ↔ sat w i (.always φ)` (definitional, stated for documentation)

- [ ] **Step 1: Write failing uses** in `Examples.lean`:

```lean
example : Safe (.always (.atom (fun n : Nat => n > 0))) := by repeat constructor
example (w : Nat → Nat) (h : ∀ k, w k > 0) : satF (prefix w 5) 0 (.always (.atom (· > 0))) = true :=
  safe_prefix (by repeat constructor) ((sat_always_iff).2 fun j _ => by simp [sat_atom_iff, h]) (by decide)
example : satF [3,1,2] 0 (.always (.atom (· > 0))) = [3,1,2].all (· > 0) := satF_always_atom
```

- [ ] **Step 2: Run to verify failure.** `BUILD DEPS …/Temporal.lean …/Examples.lean` → `FAIL` (unknown `Safe`).
- [ ] **Step 3: Implement `Bridge.lean`.** Prove `safe_prefix_at` by induction on `Safe` generalising `i`. For `wuntil`: from the infinite `until` witness `k`, case `k < n` gives the finite `until`, case `k ≥ n` gives finite `always` on `[i, n)`. Prove `cosafe_prefix_at` by induction on `CoSafe`; the `i < n` hypothesis is what rules out the true-out-of-range negated atom.
- [ ] **Step 4: Run.** `BUILD DEPS …/Temporal.lean …/Bridge.lean …/Examples.lean` → all `ok`.
- [ ] **Step 5: Commit.** `git commit -s -m "feat(temporal): prove safety and co-safety prefix theorems"`

### Task 3: Systems, runs, proof rules and fairness (`System.lean`)

**Files:**
- Create: `packages/temporal/formal/System.lean`
- Modify: `packages/temporal/formal/Examples.lean`

**Interfaces:**
- Consumes: Tasks 1–2.
- Produces:
  - `structure System (σ ι ο : Type) where init : σ; step : σ → ι → σ × ο`
  - `structure Rec (σ ι ο : Type) where pre : σ; input : ι; post : σ; out : ο`
  - `def recAt (sys) (s : σ) (i : ι) : Rec σ ι ο := ⟨s, i, (sys.step s i).1, (sys.step s i).2⟩`
  - `def statesFrom (sys) (s : σ) (u : Nat → ι) : Nat → σ` (`0 ↦ s`, `n+1 ↦ (sys.step (statesFrom n) (u n)).1`)
  - `def runFrom (sys) (s) (u) : Nat → Rec σ ι ο := fun n => recAt sys (statesFrom sys s u n) (u n)`; `def run sys u := runFrom sys sys.init u`
  - `def runF (sys) (s : σ) : List ι → List (Rec σ ι ο)`; `def finalState (sys) (s : σ) : List ι → σ`
  - `theorem runFrom_link : (runFrom sys s u (n+1)).pre = (runFrom sys s u n).post`
  - `theorem runF_prefix : runF sys s ((List.range n).map u) = prefix (runFrom sys s u) n`
  - `theorem invariant_rule (P : σ → Bool) (Good : ι → Bool) (h0 : P s = true) (hstep : ∀ s i, Good i = true → P s = true → P (sys.step s i).1 = true) (hu : ∀ n, Good (u n) = true) : ∀ n, P (statesFrom sys s u n) = true`
  - `theorem step_rule (Q : Rec σ ι ο → Bool) (P : σ → Bool) (Good : ι → Bool) (h0 hstep hu as above) (hq : ∀ s i, Good i = true → P s = true → Q (recAt sys s i) = true) : sat (runFrom sys s u) 0 (.always (.atom Q))` (use `P := fun _ => true`, `Good := fun _ => true` for unconditional properties)
  - `theorem ranking_rule (r : Nat → Rec σ ι ο) (hlink : ∀ n, (r (n+1)).pre = (r n).post) (μ : σ → Nat) (helpful goal : Rec σ ι ο → Bool) (n0 : Nat) (hmono : ∀ n ≥ n0, μ (r n).post ≤ μ (r n).pre) (hdec : ∀ n ≥ n0, helpful (r n) = true → 0 < μ (r n).pre → μ (r n).post < μ (r n).pre) (hinf : ∀ n, ∃ m ≥ n, helpful (r m) = true) (hgoal : ∀ n, μ (r n).pre = 0 → goal (r n) = true) : sat r 0 (.eventually (.atom goal))`
  - fairness: `def infOften (φ : LTL α) := LTL.always (LTL.eventually φ)`, `def WF (en tk : LTL α) := LTL.imp (.eventually (.always en)) (.always (.eventually tk))`, `def SF (en tk : LTL α) := LTL.imp (.always (.eventually en)) (.always (.eventually tk))`
  - `theorem sat_infOften_atom_iff : sat w 0 (infOften (.atom p)) ↔ ∀ n, ∃ m ≥ n, p (w m) = true`; `theorem sat_eventually_always_iff : sat w 0 (.eventually (.always φ)) ↔ ∃ T, ∀ n ≥ T, sat w n φ`

- [ ] **Step 1: Write failing examples** on a counter system `ctr : System Nat Bool Unit := ⟨0, fun s b => (if b then s+1 else s, ())⟩`:

```lean
example : runF ctr 0 [true, false, true] |>.map (·.post) = [1, 1, 2] := by decide
example (u : Nat → Bool) : sat (runFrom ctr 0 u) 0 (.always (.atom fun r => decide (r.pre ≤ r.post))) :=
  step_rule _ (fun _ => true) (fun _ => true) rfl (fun _ _ _ _ => rfl) (fun _ => rfl) (by intro s b _ _; cases b <;> simp [recAt, ctr])
example (u : Nat → Bool) (h : ∀ n, ∃ m ≥ n, u m = true) : sat (runFrom ctr 0 u) 0 (infOften (.atom fun r => r.input)) :=
  sat_infOften_atom_iff.2 (by simpa [runFrom, recAt] using h)
```

- [ ] **Step 2: Run to verify failure.** `BUILD DEPS …/Temporal.lean …/Bridge.lean …/Examples.lean` → `FAIL`.
- [ ] **Step 3: Implement `System.lean`.** `ranking_rule`: strong induction on `μ (r n0).pre`; from any `n ≥ n0` with `μ > 0`, `hinf` gives a later helpful step, `hmono` carries the bound to it, `hdec` decreases it.
- [ ] **Step 4: Run.** `BUILD DEPS …/Temporal.lean …/Bridge.lean …/System.lean …/Examples.lean` → all `ok`.
- [ ] **Step 5: Commit.** `git commit -s -m "feat(temporal): add systems, runs, proof rules and fairness"`

### Task 4: Lifecycle safety and deadlock-freedom (L1–L5)

**Files:**
- Create: `packages/temporal/formal/LifecycleTemporal.lean` (`import System`, `import StateMachine`)
- Modify: `packages/temporal/formal/Examples.lean`

**Interfaces:**
- Consumes: Task 3 (`System`, `Rec`, `run`, `step_rule`, `finalState`, `runF`).
- Produces:
  - `def lifecycle : System ProcessState Command Outcome := ⟨initial, step⟩`; `abbrev LRec := Rec ProcessState Command Outcome`
  - `def gateEvidence : List Evidence := [.requirementsReviewed, .traceabilityReviewed, .designReviewed, .formalSpecificationChecked, .proofChecked, .conformancePassed, .artifactBuilt]`
  - Boolean atoms `l1Atom l2Atom l3Atom l4Atom : LRec → Bool`, encoding the spec §5.1 rows L1–L4 exactly (use `decide` on the `=`/`∈` comparisons)
  - `theorem L1 (u : Nat → Command) : sat (run lifecycle u) 0 (.always (.atom l1Atom))`; likewise `L2`, `L3`, `L4`
  - `theorem L5_iterate (s : ProcessState) : (step s .iterate).2 = .accepted`
  - `def reachCmds : List Command := gateEvidence.map .recordValidated ++ [.promote, .promote, .promote]`
  - `theorem L5_reach (s : ProcessState) : (finalState lifecycle s reachCmds).phase = .transition`

- [ ] **Step 1: Write failing non-vacuity examples** (each antecedent actually occurs on a concrete run):

```lean
-- promote accepted occurs (L1), revise occurs (L2)
example : (runF lifecycle initial (reachCmds ++ [.reviseRequirements])).any
    (fun r => r.input == .promote && r.out == .accepted) = true := by decide
example : (runF lifecycle initial (reachCmds ++ [.reviseRequirements])).all l2Atom = true := by decide
example : (finalState lifecycle initial reachCmds).phase = .transition := L5_reach _
```

- [ ] **Step 2: Run to verify failure.** `BUILD DEPS …/Temporal.lean …/Bridge.lean …/System.lean …/Examples.lean` → `FAIL`.
- [ ] **Step 3: Implement L1–L4** with `step_rule` (unconditional); each `hq` is `cases i` on the command plus `simp [step, recAt, …]`. **Implement L5_reach** by `cases s.phase` (four cases), using that `recordValidated` prepends to `verified` and that `gateSatisfied` uses `List.contains`.
- [ ] **Step 4: Run.** `BUILD DEPS …/Temporal.lean …/Bridge.lean …/System.lean …/LifecycleTemporal.lean …/Examples.lean` → all `ok`.
- [ ] **Step 5: Commit.** `git commit -s -m "feat(temporal): prove lifecycle safety and deadlock-freedom (L1-L5)"`

### Task 5: Lifecycle liveness under fairness and necessity (L6)

**Files:**
- Modify: `packages/temporal/formal/LifecycleTemporal.lean`, `packages/temporal/formal/Examples.lean`

**Interfaces:**
- Consumes: Task 4 (`lifecycle`, `gateEvidence`), Task 3 (`sat_eventually_always_iff`, `sat_infOften_atom_iff`, `invariant_rule`, `statesFrom`).
- Produces:
  - `def atTransition : LRec → Bool := fun r => decide (r.post.phase = .transition)`
  - `theorem L6 (u : Nat → Command) (hrev : ∃ T, ∀ n ≥ T, u n ≠ .reviseRequirements) (hrec : ∀ e ∈ gateEvidence, ∀ n, ∃ m ≥ n, u m = .recordValidated e) (hpro : ∀ n, ∃ m ≥ n, u m = .promote) : sat (run lifecycle u) 0 (.eventually (.atom atTransition))`
  - `def l6Assumptions : LTL LRec` (`and` of: `.eventually (.always (.atom (r.input ≠ revise)))`, `LTL.all (gateEvidence.map fun e => infOften (.atom (r.input = .recordValidated e)))`, `infOften (.atom (r.input = .promote))`)
  - `theorem L6_ltl (u) : sat (run lifecycle u) 0 (.imp l6Assumptions (.eventually (.atom atTransition)))`
  - Necessity streams and theorems (`¬` reaching `transition` at any position):
    - `uRevise : Nat → Command`, period 9: index 0 `reviseRequirements`, 1–7 `recordValidated` of `gateEvidence` in order, 8 `promote`. `theorem L6_needs_no_revise : ∀ n, (statesFrom lifecycle initial uRevise n).phase ≠ .transition` (and `uRevise` satisfies `hrec`, `hpro`)
    - `uNoPromote`, period 7: the seven records. `theorem L6_needs_promote` (satisfies `hrev`, `hrec`)
    - `uNoArtifact`, period 7: the first six records then `promote`. `theorem L6_needs_evidence` (satisfies `hrev`, `hpro`; violates `hrec` for `.artifactBuilt`)
  - Non-vacuity: `uFair`, period 8: seven records then `promote`; `theorem uFair_assumptions : (∃ T, …) ∧ (∀ e ∈ gateEvidence, …) ∧ (∀ n, …)` matching L6's hypotheses.

- [ ] **Step 1: Write failing examples:** `example : sat (run lifecycle uFair) 0 (.eventually (.atom atTransition)) := L6 uFair uFair_assumptions.1 uFair_assumptions.2.1 uFair_assumptions.2.2`, plus `#check @L6_needs_no_revise`, `#check @L6_needs_promote`, `#check @L6_needs_evidence`.
- [ ] **Step 2: Run to verify failure** (`BUILD` as in Task 4 → `FAIL`).
- [ ] **Step 3: Implement L6.** After `T`: (i) evidence in `verified` never disappears (L4 with no revise), (ii) phase never decreases. Prove by induction on the remaining phase count: from a position `n ≥ T` with phase `p ≠ transition`, take the latest of the recording times after `n` for the evidence `p`'s gate needs (from `hrec`), then a `promote` after that (from `hpro`); at that promote the gate holds, so the phase advances. `L6_ltl` unfolds the LTL assumptions via the Task 2–3 iff-lemmas.
- [ ] **Step 4: Implement necessity.** `L6_needs_promote`: `invariant_rule` with `P := phase = inception`, `Good := ≠ promote`. `L6_needs_evidence`: `invariant_rule` with `P := !verified.contains .artifactBuilt && phase ≠ transition`, `Good := ≠ recordValidated .artifactBuilt ∧ ≠ revise`. `L6_needs_no_revise`: an invariant indexed by `n % 9`: if `n % 9 = 0` then phase ∈ {inception, elaboration}, otherwise phase = inception; prove by induction on `n` with case analysis on `n % 9`.
- [ ] **Step 5: Run.** Same `BUILD` as Task 4 → all `ok`.
- [ ] **Step 6: Commit.** `git commit -s -m "feat(temporal): prove lifecycle liveness under fairness and necessity (L6)"`

### Task 6: DriverPass safety, response, progress and race (D1–D3, D4a, D5)

**Files:**
- Create: `packages/temporal/formal/DriverPassTemporal.lean` (`import System`, `import Transactions`; `open DriverPassTx`)
- Modify: `packages/temporal/formal/Examples.lean`

**Interfaces:**
- Consumes: Tasks 2–3; `DriverPassTx.assignTx`, `roster`, `slotsOf`, `nodupNat`, `NoDoubleBooking`, `tx_preserves_no_double_booking`, `tx_allocations`, `racyPair`, `demo`.
- Produces:
  - `abbrev Req := Nat × Nat × Option Fault`; `def driverpass : System Db Req Response := ⟨demo, fun db r => assignTx db r.1 r.2.1 r.2.2⟩`; `abbrev DRec := Rec Db Req Response`
  - `def allocOkB (db : Db) : Bool := db.allocations.all fun a => nodupNat (slotsOf db.allocations a.1)`; `theorem allocOkB_iff : allocOkB db = true ↔ NoDoubleBooking db`
  - `def isDecided : Response → Bool`; atoms `d2Atom d3Atom : DRec → Bool` per spec §5.2 (D2: `isDecided r.out || r.post == r.pre`, and allocations of `pre` all in `post`; D3: if `(roster r.pre r.input.1).isSome && r.input.2.2 == none` then `out = decided d _` with `post.audit = (i, slot, d) :: pre.audit`)
  - `theorem D1 (db0 : Db) (h : NoDoubleBooking db0) (u : Nat → Req) : sat (runFrom driverpass db0 u) 0 (.always (.atom fun r => allocOkB r.post))`
  - `theorem D2 (db0 u) : sat (runFrom driverpass db0 u) 0 (.always (.atom d2Atom))`; `theorem D3 (db0 u) : … (.always (.atom d3Atom))`
  - `theorem D4a (db : Db) (i slot : Nat) (r : Roster) (hr : roster db i = some r) (hon : r.offDuty = false) (hfree : slot ∉ slotsOf db.allocations i) : ∃ r', (assignTx db i slot none).2 = .decided .accepted r'`
  - `def racyTrace : List Db := [demo, racyPair demo 7 42]`; `theorem D5 : satF racyTrace 0 (.always (.atom allocOkB)) = false`; `theorem D5_extensions (w : Nat → Db) (h : prefix w 2 = racyTrace) : ¬ sat w 0 (.always (.atom allocOkB))`

- [ ] **Step 1: Write failing non-vacuity examples:**

```lean
def dpReqs : List Req := [(7, 42, none), (7, 42, none), (7, 43, some .atCommit), (9, 1, none)]
example : (runF driverpass demo dpReqs).all d3Atom = true := by decide
example : (runF driverpass demo dpReqs).any (fun r => !isDecided r.out) = true := by decide  -- D2 antecedent
example : (runF driverpass demo dpReqs).any (fun r => r.out matches .decided .accepted _) = true := by decide
#check @D5_extensions
```

- [ ] **Step 2: Run to verify failure.** `BUILD DEPS …/Temporal.lean …/Bridge.lean …/System.lean …/Examples.lean` → `FAIL`.
- [ ] **Step 3: Implement.** D1: `step_rule` with `P := allocOkB`, using `allocOkB_iff` and `tx_preserves_no_double_booking`. D2: from `tx_allocations` and the all-or-nothing shape of `assignTx`. D3: unfold `assignTx` with `fault = none`. D4a: unfold `allocate` with `hon`, `hfree`. D5: `by decide`. D5_extensions: contrapositive of `safe_prefix` with `n = 2`.
- [ ] **Step 4: Run.** `BUILD DEPS …/Temporal.lean …/Bridge.lean …/System.lean …/LifecycleTemporal.lean …/DriverPassTemporal.lean …/Examples.lean` → all `ok`.
- [ ] **Step 5: Commit.** `git commit -s -m "feat(temporal): prove DriverPass safety, response, progress and race (D1-D5)"`

### Task 7: DriverPass liveness under retry fairness (D4b)

**Files:**
- Modify: `packages/temporal/formal/DriverPassTemporal.lean`, `packages/temporal/formal/Examples.lean`

**Interfaces:**
- Consumes: Task 6 (`driverpass`, `D2`, `D4a`), Task 3 (`sat_eventually_always_iff`, `statesFrom`).
- Produces:
  - `theorem instructors_stable (db : Db) (q : Req) : (driverpass.step db q).1.instructors = db.instructors`
  - `theorem D4b (db0 : Db) (i slot : Nat) (r0 : Roster) (hr : roster db0 i = some r0) (hon : r0.offDuty = false) (u : Nat → Req) (hinf : ∀ n, ∃ m ≥ n, u m = (i, slot, none)) : sat (runFrom driverpass db0 u) 0 (.eventually (.always (.atom fun r => (slotsOf r.post.allocations i).contains slot)))`

- [ ] **Step 1: Write the failing non-vacuity example:** `example : sat (runFrom driverpass demo (fun _ => (7, 42, none))) 0 (.eventually (.always (.atom fun r => (slotsOf r.post.allocations 7).contains 42))) := D4b demo 7 42 ⟨false, []⟩ (by decide) rfl _ (fun n => ⟨n, Nat.le_refl _, rfl⟩)`
- [ ] **Step 2: Run to verify failure** (`BUILD` as Task 6 → `FAIL`).
- [ ] **Step 3: Implement D4b.** `instructors_stable` gives that `i` stays on duty at every position. Take the first `m` from `hinf`: after step `m` the slot is in `slotsOf … i` (accepted by D4a, or already present, which is the duplicate case). Allocations only grow (D2), so it stays; conclude with `sat_eventually_always_iff`, `T = m`.
- [ ] **Step 4: Run.** Same `BUILD` as Task 6 → all `ok`.
- [ ] **Step 5: Commit.** `git commit -s -m "feat(temporal): prove DriverPass liveness under retry fairness (D4b)"`

### Task 8: Axiom audit and the verify script

**Files:**
- Create: `packages/temporal/scripts/check_axioms.py`, `packages/temporal/scripts/verify.py`
- Create: `packages/temporal/tests/test_check_axioms.py`
- Modify: `packages/temporal/formal/Examples.lean` (append `#print axioms` for every name in `REQUIRED` below)

**Interfaces:**
- Produces:
  - `check_axioms.py`: `REQUIRED = ["safe_prefix", "cosafe_prefix", "L1", "L2", "L3", "L4", "L5_reach", "L6", "L6_ltl", "L6_needs_no_revise", "L6_needs_promote", "L6_needs_evidence", "D1", "D2", "D3", "D4a", "D4b", "D5", "D5_extensions"]`; `ALLOWED = {"propext", "Quot.sound", "Classical.choice"}`; `def parse_axioms(log: str) -> dict[str, set[str]]` (handles `'X' depends on axioms: [a, b]` spread over several lines and `'X' does not depend on any axioms`; keys are names with the namespace prefix stripped); `def scan_sources(paths: list[Path]) -> list[str]` (problems for `sorry`, a line starting with `axiom`, or `native_decide`); `def check(log: str, sources: list[Path]) -> list[str]` (problems: missing required theorem, axiom outside `ALLOWED`, source problems); CLI `check_axioms.py LOGFILE` exits 1 and prints problems, else prints `axioms ok (<n> theorems)`.
  - `verify.py`: runs the full `BUILD DEPS` + the six temporal files in order using `sys.executable`, writes the combined output to a temp log, runs `check(...)` on it and on `packages/temporal/formal/*.lean`; exits non-zero on any failure. Run from repo root: `python packages/temporal/scripts/verify.py`.

- [ ] **Step 1: Write failing tests** in `test_check_axioms.py` (stdlib `unittest`):
  - `test_parses_single_line`: `"'Architecton.Temporal.L1' depends on axioms: [propext]"` → `{"L1": {"propext"}}`
  - `test_parses_wrapped_list`: the same entry with `[propext,\n  Classical.choice,\n  Quot.sound]` → three axioms
  - `test_no_axioms`: `"'Architecton.Temporal.D5' does not depend on any axioms"` → `{"D5": set()}`
  - `test_rejects_extra_axiom`: an entry with `Lean.ofReduceBool` → a problem mentioning it
  - `test_missing_required`: a log without `D4b` → a problem naming `D4b`
  - `test_scan_flags_sorry_and_native_decide`: temp file containing `sorry` and `native_decide` → two problems
- [ ] **Step 2: Run to verify failure.** `python -m unittest discover -s packages/temporal/tests -v` → errors (module not found).
- [ ] **Step 3: Implement both scripts.**
- [ ] **Step 4: Run.** The unit tests → all `OK`. Then `python packages/temporal/scripts/verify.py` on Windows → every file `ok` and `axioms ok (19 theorems)`, exit 0.
- [ ] **Step 5: Commit.** `git commit -s -m "feat(temporal): add axiom audit and verify script"`

### Task 9: CI, evidence ledger and documentation

**Files:**
- Create: `.github/workflows/verify-temporal.yml`, `packages/temporal/README.md`
- Modify: `evidence/checks.json`, `README.md` (roadmap bullet “Temporal/runtime verification” and the intro sentence of that section), `packages/README.md`, `docs/assurance.md`, `CHANGELOG.md`

**Interfaces:**
- Consumes: Task 8 (`verify.py`, the test directory).

- [ ] **Step 1: Workflow.** Copy the Lean install steps from `.github/workflows/verify-lifecycle.yml`. Triggers (push and pull_request, plus `workflow_dispatch`) on paths `packages/temporal/**`, `packages/lifecycle/formal/**`, `examples/driverpass/formal/**`, `packages/ledger/scripts/lean_build.py`, `.github/workflows/verify-temporal.yml`. `runs-on: ubuntu-24.04`. Steps from the repo root: `python3 -m unittest discover -s packages/temporal/tests -v`, then `python3 packages/temporal/scripts/verify.py`.
- [ ] **Step 2: Evidence check.** Append to `evidence/checks.json` `checks`: `{"id": "temporal-lean", "description": "Lean temporal core: LTL semantics, bridge theorems, lifecycle L1-L6 and DriverPass D1-D5", "argv": ["python3", "packages/temporal/scripts/verify.py"], "inputs": ["packages/temporal/formal/*.lean", "packages/temporal/scripts/*.py", "packages/lifecycle/formal/*.lean", "examples/driverpass/formal/*.lean", "packages/ledger/scripts/lean_build.py"]}`. Run `python -m unittest discover -s packages/ledger/tests -v` → `OK` (the registry still parses).
- [ ] **Step 3: Docs.** `packages/temporal/README.md`: purpose, a property table (id, kind, plain-language statement, assumptions) for L1–L6 and D1–D5, the build command, and the assurance boundary from spec §9. Root README and `packages/README.md`: temporal/runtime verification becomes “partially implemented (Lean temporal core, see packages/temporal)”, with runtime monitoring, TLA+ concurrency and distributed consistency listed as still open. `docs/assurance.md`: a “Temporal properties” section with spec §9's three bullets. `CHANGELOG.md` Unreleased → Added: one line for the temporal core.
- [ ] **Step 4: Check that the models were not edited.** `git diff --exit-code main -- packages/lifecycle/formal examples/driverpass/formal` → no output, exit 0. Run `python packages/temporal/scripts/verify.py` once more → exit 0.
- [ ] **Step 5: Commit.** `git commit -s -m "ci(temporal): add workflow, evidence check and docs"`
