#!/usr/bin/env python3
"""Generate the narrow Lean phase gate from a reviewed JSON policy.

This generator intentionally has a CLOSED semantic vocabulary. It rejects
unknown evidence or phases rather than guessing their meaning. Its correctness
is tested, not formally established.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PHASES = ("inception", "elaboration", "construction", "transition")
EVIDENCE = (
    "requirementsReviewed", "traceabilityReviewed", "designReviewed",
    "formalSpecificationChecked", "proofChecked", "conformancePassed",
    "artifactBuilt", "deploymentValidated",
)


def load_policy():
    path = ROOT / "requirements/policy.json"
    raw = path.read_bytes()
    obj = json.loads(raw)
    if obj.get("schema_version") != "1.0.0":
        raise ValueError("Unsupported policy schema version")
    if obj.get("phase_order") != list(PHASES):
        raise ValueError("Phase ordering is an explicit governance decision; do not reorder silently")
    if obj.get("evidence_kinds") != list(EVIDENCE):
        raise ValueError("Evidence vocabulary changed; explicit Lean domain review is required")
    rules = obj.get("required_evidence")
    if not isinstance(rules, dict) or set(rules) != set(PHASES):
        raise ValueError("Every lifecycle phase must have exactly one gate")
    for phase, allowed in rules.items():
        if not isinstance(allowed, list) or len(set(allowed)) != len(allowed):
            raise ValueError("Gate must be an ordered list of distinct evidence kinds")
        if any(e not in EVIDENCE for e in allowed):
            raise ValueError(f"Unknown evidence kind in {phase}")
    if any(not rules[p] for p in PHASES[:-1]) or rules["transition"]:
        raise ValueError("Each nonterminal phase needs evidence; transition has no successor")
    return obj, hashlib.sha256(raw).hexdigest()[:16]


def generate(obj, digest):
    lines = [
        f"/-! Auto-generated from requirements/policy.json (SHA-256 prefix {digest}).",
        "DO NOT EDIT: python3 scripts/generate_policy.py --write",
        "The gate encodes reviewed policy conditions; it is not itself a proof",
        "that an actual artifact was verified by a trusted system. -/",
        "import ArchitectonLifecycle",
        "namespace Architecton.Lifecycle",
        "",
        "/-- Decidable phase-promotion gate under the reviewed policy. -/",
        "def gateSatisfied (s : ProcessState) : Bool :=",
        "  match s.phase with",
    ]
    for phase in PHASES:
        required = obj["required_evidence"][phase]
        if not required:
            lines.append(f"  | .{phase} => false")
            continue
        lines.append(f"  | .{phase} =>")
        conditions = [f"s.verified.contains Evidence.{e}" for e in required]
        expression = conditions[0]
        for condition in conditions[1:]:
            expression = f"({expression} && {condition})"
        lines.append("      " + expression)
    lines.extend([
        "", "/-- Proposition-level reading of the executable Boolean gate. -/",
        "def Gate (s : ProcessState) : Prop := gateSatisfied s = true",
        "", "end Architecton.Lifecycle", "",
    ])
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    action = ap.add_mutually_exclusive_group(required=True)
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    args = ap.parse_args()
    obj, digest = load_policy()
    output = ROOT / "formal/Policy.lean"
    expected = generate(obj, digest)
    if args.write:
        output.write_text(expected)
        print(f"WROTE {output.relative_to(ROOT)}; policy SHA-256 prefix {digest}")
    elif not output.exists() or output.read_text() != expected:
        raise SystemExit("FAIL: generated Lean gate differs from requirements/policy.json")
    else:
        print("PASS: policy schema and generated Lean gate in sync")


if __name__ == "__main__":
    main()
