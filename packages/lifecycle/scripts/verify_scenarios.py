#!/usr/bin/env python3
"""Finite scenario checks of the reviewed phase-gate policy.

Independent Python reference interpreter: observational checks only, not proof
of Lean/Python equivalence. The Lean kernel checks universal properties.
"""
import json
import sys
import itertools
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from generate_policy import load_policy  # noqa: E402


def initial():
    return {"phase": "inception", "iteration": 0, "revision": 0,
            "verified": [], "archive": []}


def run_action(state, action, policy):
    old = {"phase": state["phase"], "iteration": state["iteration"],
           "revision": state["revision"], "verified": state["verified"][:],
           "archive": state["archive"][:]}
    s = {**old}
    kind = action["action"]
    if kind == "recordValidated":
        evidence = action["evidence"]
        if evidence not in policy["evidence_kinds"]:
            raise ValueError(f"Unsupported evidence: {evidence}")
        s["verified"] = [evidence] + s["verified"]
        return s, "accepted"
    if kind == "iterate":
        s["iteration"] += 1
        return s, "accepted"
    if kind == "reviseRequirements":
        s["archive"] = [[s["revision"], s["verified"][:]]] + s["archive"]
        s["revision"] += 1
        s["iteration"] += 1
        s["phase"] = "inception"
        s["verified"] = []
        return s, "accepted"
    if kind == "promote":
        phases = policy["phase_order"]
        index = phases.index(s["phase"])
        if index == len(phases) - 1:
            return s, "blocked"
        if not all(e in s["verified"] for e in policy["required_evidence"][s["phase"]]):
            return s, "blocked"
        s["phase"] = phases[index + 1]
        return s, "accepted"
    raise ValueError(f"Unsupported command: {kind}")


def main():
    policy, _ = load_policy()
    suite = json.loads((ROOT / "contracts/scenarios.json").read_text())
    assert suite["schema_version"] == "1.0.0"
    ids = set()
    for case in suite["cases"]:
        if case["id"] in ids:
            raise AssertionError("Duplicate scenario ID")
        ids.add(case["id"])
        s = initial()
        outcome = None
        for command in case["commands"]:
            old = {**s, "verified": s["verified"][:], "archive": s["archive"][:]}
            s, outcome = run_action(s, command, policy)
            if outcome == "blocked" and s != old:
                raise AssertionError(f"{case['id']}: blocked request mutated state")
            if command["action"] == "promote" and outcome == "accepted":
                assert policy["phase_order"].index(s["phase"]) == policy["phase_order"].index(old["phase"]) + 1
            if command["action"] == "reviseRequirements":
                assert s["verified"] == [] and s["phase"] == "inception"
        expected = case["expect"]
        observables = {**s, "outcome": outcome,
                       "verified_count": len(s["verified"]),
                       "archive_count": len(s["archive"])}
        for key, expected_value in expected.items():
            if observables.get(key) != expected_value:
                raise AssertionError(f"{case['id']}: {key} expected {expected_value!r}, got {observables.get(key)!r}")
    # Finite safety sweep supplements (and must not be confused with) Lean proofs.
    # Every phase and every subset of the eight supported evidence kinds.
    sweep_count = 0
    phases = policy["phase_order"]
    for phase in phases:
        for bits in itertools.product((False, True), repeat=len(policy["evidence_kinds"])):
            evidence = [kind for kind, included in zip(policy["evidence_kinds"], bits) if included]
            s = {**initial(), "phase": phase, "verified": evidence}
            promoted, outcome = run_action(s, {"action": "promote"}, policy)
            has_gate = all(kind in evidence for kind in policy["required_evidence"][phase])
            expected_accepted = has_gate and phase != "transition"
            assert (outcome == "accepted") == expected_accepted
            if expected_accepted:
                assert phases.index(promoted["phase"]) == phases.index(phase) + 1
                assert promoted["verified"] == evidence
            else:
                assert promoted == s, "Failed promotion changed state"
            revised, decision = run_action(s, {"action": "reviseRequirements"}, policy)
            assert decision == "accepted" and revised["verified"] == []
            assert revised["phase"] == "inception" and revised["revision"] == 1
            assert revised["archive"][0] == [0, evidence]
            iterated, decision = run_action(s, {"action": "iterate"}, policy)
            assert decision == "accepted" and iterated["phase"] == phase
            assert iterated["verified"] == evidence and iterated["iteration"] == 1
            sweep_count += 1
    print(f"PASS: {len(ids)} contract scenarios + {sweep_count} bounded evidence/phase states")


if __name__ == "__main__":
    main()
