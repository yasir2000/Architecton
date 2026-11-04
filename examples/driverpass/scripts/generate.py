#!/usr/bin/env python3
"""Narrow, deterministic policy -> Lean/Rust adapter for the DriverPass PoC.

NOT a general-purpose verified requirements compiler. Reject unknown policy vocabulary.
Use --check in CI to catch drift between the canonical decision table and generated code.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def lean_roster(s):
    slots = ", ".join(str(x) for x in s["slots"])
    return f'{{ offDuty := {str(s["off_duty"]).lower()}, slots := [{slots}] }}'


def generate():
    policy_file = ROOT / "requirements/policy.json"
    policy = json.loads(policy_file.read_text(encoding="utf-8"))
    scenarios = json.loads((ROOT / "contracts/scenarios.json").read_text(encoding="utf-8"))
    guards = policy["ordered_guards"]
    guard_pairs = [(g["predicate"], g["decision"]) for g in guards]
    # This explicit vocabulary is the POC's typed semantic subset. Unknown words fail hard.
    if guard_pairs != [("off_duty", "off_duty"), ("slot_exists", "duplicate")]:
        raise ValueError("Unsupported guard sequence: semantic mapping requires review")
    if policy["otherwise"] != {
        "requirement_id": "BR-003", "decision": "accepted",
        "effect": "prepend_slot", "meaning": "Accept and prepend a previously unassigned slot."
    }:
        raise ValueError("Unsupported terminal effect: semantic mapping requires review")
    if policy["entity"] != "InstructorRoster" or policy["workflow"] != "assign_slot":
        raise ValueError("Unsupported entity or workflow")
    # Hash with LF line endings so Windows (CRLF) and Linux checkouts agree.
    digest = hashlib.sha256(policy_file.read_bytes().replace(b"\r\n", b"\n")).hexdigest()[:16]
    lean = f'''/- Auto-generated from requirements/policy.json (SHA-256 prefix {digest}).
   DO NOT EDIT: python3 scripts/generate.py -/

inductive Decision where
  | accepted
  | offDuty
  | duplicate
  deriving Repr, DecidableEq

structure Roster where
  offDuty : Bool
  slots : List Nat
  deriving Repr, DecidableEq

/-- The policy's ordered decision table. A pure transition relation. -/
def allocate (s : Roster) (slot : Nat) : Roster × Decision :=
  if s.offDuty then
    (s, Decision.offDuty)
  else if s.slots.contains slot then
    (s, Decision.duplicate)
  else
    ({{ s with slots := slot :: s.slots }}, Decision.accepted)
'''
    rust = f'''// Auto-generated from requirements/policy.json (SHA-256 prefix {digest}).
// DO NOT EDIT: python3 scripts/generate.py
use serde::{{Deserialize, Serialize}};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Roster {{
    pub off_duty: bool,
    pub slots: Vec<i64>,
}}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Decision {{
    Accepted,
    OffDuty,
    Duplicate,
}}

// BR-001 -> BR-002 -> BR-003, with exactly the same guard priority as Lean.
pub fn allocate(s: &Roster, slot: i64) -> (Roster, Decision) {{
    if s.off_duty {{
        (s.clone(), Decision::OffDuty)
    }} else if s.slots.contains(&slot) {{
        (s.clone(), Decision::Duplicate)
    }} else {{
        let mut result = s.clone();
        result.slots.insert(0, slot);
        (result, Decision::Accepted)
    }}
}}
'''
    examples = [f'/- Generated from contracts/scenarios.json. Checked by Lean `decide`. -/\nimport DriverPass\n']
    valid_decisions = {"accepted": "accepted", "off_duty": "offDuty", "duplicate": "duplicate"}
    for s in scenarios:
        if not isinstance(s["slot_id"], int) or s["slot_id"] < 0 or s["slot_id"] > 2**63 - 1:
            raise ValueError("Scenario slot outside the safe shared Nat/i64 domain")
        for roster in [s["before"], s["expected"]["roster"]]:
            if not isinstance(roster["off_duty"], bool) or not all(isinstance(x, int) and 0 <= x <= 2**63 - 1 for x in roster["slots"]):
                raise ValueError("Scenario roster invalid")
        dec = valid_decisions[s["expected"]["decision"]]
        examples.append(f'-- {s["name"]}\nexample : allocate {lean_roster(s["before"])} {s["slot_id"]} =\n  ({lean_roster(s["expected"]["roster"])}, Decision.{dec}) := by decide\n')
    generated = {
        ROOT / "formal/DriverPass.lean": lean,
        ROOT / "formal/Scenarios.lean": "\n".join(examples),
        ROOT / "backend/src/domain.rs": rust,
    }
    return generated


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="Fail if generated outputs drift")
    args = parser.parse_args()
    generated = generate()
    stale = [str(path.relative_to(ROOT)) for path, content in generated.items()
             if not path.exists() or path.read_text(encoding="utf-8") != content]
    if args.check:
        if stale:
            raise SystemExit("Generated files drifted: " + ", ".join(stale))
        print("All generated policy adapters and Lean scenarios are up-to-date.")
    else:
        for path, content in generated.items():
            path.write_text(content, encoding="utf-8", newline="\n")
            print("Generated", path.relative_to(ROOT))


if __name__ == "__main__":
    main()
