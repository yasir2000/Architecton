import ArtifactIR

/-!
Negative checks: `wellFormed` must REJECT each of these broken models.
Each `example` is kernel-checked, so a regression that makes the checker
accept one of them breaks the build.
-/

open Architecton.IR

private def art : Artifact := { id := "ART-1", path := "x.md", sha256 := "" }
private def src : List Anchor := [⟨"ART-1", "anchor", .source⟩]

private def baseTr : Transition where
  id := "T1"
  params := [("n", .nat)]
  guards := [{ requirement := "R1", cond := .var "flag", outcome := "blocked" }]
  otherwiseRequirement := "R1"
  otherwiseOutcome := "ok"
  effect := [{ var := "xs", value := .cons (.param "n") (.var "xs") }]

/-- A small model that IS well-formed; each negative case changes one thing. -/
private def base : Model where
  goals := [{ id := "G0", parent := none, provenance := src }]
  requirements := [{ id := "R1", kind := .business, goals := ["G0"], provenance := src }]
  risks := [{ id := "K1", status := .mitigated, mitigatedBy := ["R1"], provenance := src }]
  stateVars := [("flag", .bool), ("xs", .natList)]
  transitions := [baseTr]
  invariants := [{ id := "I1", requirement := "R1", body := .nodup (.var "xs") }]
  artifacts := [art]

example : wellFormed base = true := by decide

/-- A guard that is a number, not a Boolean. -/
example : wellFormed { base with transitions := [{ baseTr with
    guards := [{ requirement := "R1", cond := .param "n", outcome := "blocked" }] }] } = false := by
  decide

/-- An effect that writes a Bool into a `List Nat` variable. -/
example : wellFormed { base with transitions := [{ baseTr with
    effect := [{ var := "xs", value := .litBool true }] }] } = false := by
  decide

/-- An invariant that mentions a transition parameter. -/
example : wellFormed { base with invariants :=
    [{ id := "I1", requirement := "R1", body := .contains (.var "xs") (.param "n") }] } = false := by
  decide

/-- A requirement that refines no goal. -/
example : wellFormed { base with requirements :=
    [{ id := "R1", kind := .business, goals := [], provenance := src }] } = false := by
  decide

/-- A requirement that refines an undeclared goal. -/
example : wellFormed { base with requirements :=
    [{ id := "R1", kind := .business, goals := ["G9"], provenance := src }] } = false := by
  decide

/-- A cycle in goal refinement. -/
example : wellFormed { base with goals :=
    [{ id := "G0", parent := some "G1", provenance := src },
     { id := "G1", parent := some "G0", provenance := src }] } = false := by
  decide

/-- A "mitigated" risk with no mitigating requirement. -/
example : wellFormed { base with risks :=
    [{ id := "K1", status := .mitigated, mitigatedBy := [], provenance := src }] } = false := by
  decide

/-- A provenance anchor into an undeclared artifact. -/
example : wellFormed { base with goals :=
    [{ id := "G0", parent := none, provenance := [⟨"ART-9", "anchor", .source⟩] }] } = false := by
  decide

/-- Two elements sharing one identifier. -/
example : wellFormed { base with risks :=
    [{ id := "R1", status := .open, mitigatedBy := [], provenance := src }] } = false := by
  decide
