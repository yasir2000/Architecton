#!/usr/bin/env python3
"""Build and audit the Lean temporal core.

Kernel-checks the imported lifecycle and DriverPass models and every temporal
module in dependency order (via packages/ledger/scripts/lean_build.py), then
runs the axiom audit on the build output and the temporal sources.
Run from anywhere; exits non-zero on any failure.
"""
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_axioms  # noqa: E402

PATHS = ["packages/lifecycle/formal", "examples/driverpass/formal", "packages/temporal/formal"]
DEPS = [
    "packages/lifecycle/formal/ArchitectonLifecycle.lean",
    "packages/lifecycle/formal/Policy.lean",
    "packages/lifecycle/formal/StateMachine.lean",
    "examples/driverpass/formal/DriverPass.lean",
    "examples/driverpass/formal/Transactions.lean",
]
MODULES = ["Temporal", "Bridge", "System", "LifecycleTemporal", "DriverPassTemporal", "Examples"]


def build_env(base):
    """Environment for the Lean build.

    Pins the package's toolchain explicitly (ELAN_TOOLCHAIN): the build runs
    from the repo root, which has no lean-toolchain file, and CI installs elan
    without a default toolchain. Forces Python's UTF-8 mode so Windows does
    not decode Lean's UTF-8 output as cp1252.
    """
    pinned = (ROOT / "packages/temporal/lean-toolchain").read_text(encoding="utf-8").strip()
    return dict(base, ELAN_TOOLCHAIN=pinned, PYTHONUTF8="1")


def main():
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    files = DEPS + [f"packages/temporal/formal/{m}.lean" for m in MODULES]
    cmd = [sys.executable, "packages/ledger/scripts/lean_build.py"]
    for p in PATHS:
        cmd += ["--path", p]
    env = build_env(os.environ)
    proc = subprocess.run(cmd + files, cwd=ROOT, env=env, capture_output=True,
                          encoding="utf-8", errors="replace")
    log = proc.stdout + proc.stderr
    sys.stdout.write(log)
    if proc.returncode != 0:
        print("FAIL: Lean build")
        return proc.returncode
    with tempfile.NamedTemporaryFile("w", suffix=".log", delete=False, encoding="utf-8") as f:
        f.write(log)
    print(f"build log: {f.name}")
    sources = sorted((ROOT / "packages/temporal/formal").glob("*.lean"))
    problems = check_axioms.check(log, sources)
    for p in problems:
        print(f"AXIOM CHECK: {p}")
    if problems:
        return 1
    print(f"axioms ok ({len(check_axioms.REQUIRED)} theorems)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
