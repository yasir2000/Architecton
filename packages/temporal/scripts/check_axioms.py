#!/usr/bin/env python3
"""Axiom audit for the Lean temporal core.

Reads the output of building `Examples.lean` (which ends with `#print axioms`
for every main theorem) and fails if a required theorem is missing, or uses
an axiom outside Lean's standard three. Also scans the Lean sources for
`sorry`, `axiom` declarations and `native_decide` (comments are ignored).

Usage: check_axioms.py LOGFILE [SOURCE.lean ...]
"""
import re
import sys
from pathlib import Path

PREFIX = "Architecton.Temporal."

REQUIRED = [
    "safe_prefix", "cosafe_prefix",
    "L1", "L2", "L3", "L4", "L5_reach", "L6", "L6_ltl",
    "L6_needs_no_revise", "L6_needs_promote", "L6_needs_evidence",
    "D1", "D2", "D3", "D4a", "D4b", "D4b_once", "D5", "D5_extensions",
]

ALLOWED = {"propext", "Quot.sound", "Classical.choice"}

_DEPENDS = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.DOTALL)
_NONE = re.compile(r"'([^']+)' does not depend on any axioms")


def _short(name):
    return name[len(PREFIX):] if name.startswith(PREFIX) else name


def parse_axioms(log):
    """Map each theorem in `#print axioms` output to the set of its axioms."""
    result = {}
    for name, axioms in _DEPENDS.findall(log):
        result[_short(name)] = {a.strip() for a in axioms.split(",") if a.strip()}
    for name in _NONE.findall(log):
        result[_short(name)] = set()
    return result


def _strip_comments(text):
    """Remove Lean comments: nested block comments and line comments."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def scan_sources(paths):
    """Problems for `sorry`, `axiom` declarations or `native_decide`."""
    problems = []
    for path in paths:
        code = _strip_comments(Path(path).read_text(encoding="utf-8"))
        for lineno, line in enumerate(code.splitlines(), 1):
            if re.search(r"\bsorry\b", line):
                problems.append(f"{path}:{lineno}: uses sorry")
            if re.match(r"\s*(private\s+|protected\s+)?axiom\b", line):
                problems.append(f"{path}:{lineno}: declares an axiom")
            if "native_decide" in line:
                problems.append(f"{path}:{lineno}: uses native_decide")
    return problems


def check(log, sources):
    problems = []
    found = parse_axioms(log)
    for name in REQUIRED:
        if name not in found:
            problems.append(f"{name}: missing from #print axioms output")
        else:
            extra = sorted(found[name] - ALLOWED)
            if extra:
                problems.append(f"{name}: uses non-standard axioms {', '.join(extra)}")
    return problems + scan_sources(sources)


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 2
    log = Path(argv[1]).read_text(encoding="utf-8")
    problems = check(log, [Path(p) for p in argv[2:]])
    for p in problems:
        print(f"AXIOM CHECK: {p}")
    if problems:
        return 1
    print(f"axioms ok ({len(REQUIRED)} theorems)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
