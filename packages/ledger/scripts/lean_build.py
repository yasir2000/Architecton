#!/usr/bin/env python3
"""Kernel-check Lean files in order, portably (LEAN_PATH uses ';' on Windows,
':' elsewhere). Every file is compiled to a .olean next to it, so later files
can import earlier ones.

Usage: lean_build.py --path DIR [--path DIR ...] FILE.lean [FILE.lean ...]
Paths are relative to the current directory.
"""
import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--path", action="append", default=[])
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()
    lean = shutil.which("lean")
    if not lean:
        print("ERROR: lean not found on PATH")
        return 127
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(str(Path(p).resolve()) for p in args.path))
    version = subprocess.run([lean, "--version"], capture_output=True, text=True).stdout.strip()
    print(version)
    for f in args.files:
        src = Path(f)
        proc = subprocess.run([lean, "-o", str(src.with_suffix(".olean")), str(src)],
                              env=env, capture_output=True, text=True)
        sys.stdout.write(proc.stdout + proc.stderr)
        if proc.returncode != 0:
            print(f"FAIL {f}")
            return proc.returncode
        print(f"ok   {f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
