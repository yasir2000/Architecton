"""Tests for verify.py's build environment."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import verify  # noqa: E402


class BuildEnv(unittest.TestCase):
    def test_pins_the_package_toolchain(self):
        # CI installs elan with no default toolchain and runs Lean from the
        # repo root, which has no lean-toolchain file: the pin must be explicit.
        pinned = (verify.ROOT / "packages/temporal/lean-toolchain").read_text().strip()
        env = verify.build_env({})
        self.assertEqual(env["ELAN_TOOLCHAIN"], pinned)
        self.assertEqual(pinned, "leanprover/lean4:v4.35.0")

    def test_forces_utf8(self):
        self.assertEqual(verify.build_env({})["PYTHONUTF8"], "1")


if __name__ == "__main__":
    unittest.main()
