#!/usr/bin/env python3
"""Local stdlib sanity check when Rust/Lean toolchains are not installed.
This is a SCENARIO VALIDATOR, not a replacement for Lean or Rust verification.
"""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
policy = json.loads((ROOT / "requirements/policy.json").read_text())
cases = json.loads((ROOT / "contracts/scenarios.json").read_text())
assert [g["predicate"] for g in policy["ordered_guards"]] == ["off_duty", "slot_exists"]
for case in cases:
    before = case["before"]
    if before["off_duty"]:
        decision, after = "off_duty", before
    elif case["slot_id"] in before["slots"]:
        decision, after = "duplicate", before
    else:
        decision, after = "accepted", {
            "off_duty": before["off_duty"],
            "slots": [case["slot_id"], *before["slots"]],
        }
    assert {"decision": decision, "roster": after} == case["expected"], case["name"]
print(f"PASS: {len(cases)} canonical policy scenarios (Python sanity interpreter only)")
