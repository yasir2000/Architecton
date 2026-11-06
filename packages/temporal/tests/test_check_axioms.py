"""Tests for the temporal package's axiom audit."""
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import check_axioms  # noqa: E402


def full_log(skip=()):
    """A log in which every required theorem uses only standard axioms."""
    return "\n".join(
        f"'Architecton.Temporal.{n}' depends on axioms: [propext]"
        for n in check_axioms.REQUIRED if n not in skip)


class ParseAxioms(unittest.TestCase):
    def test_parses_single_line(self):
        log = "'Architecton.Temporal.L1' depends on axioms: [propext]"
        self.assertEqual(check_axioms.parse_axioms(log), {"L1": {"propext"}})

    def test_parses_wrapped_list(self):
        log = "'Architecton.Temporal.L1' depends on axioms: [propext,\n  Classical.choice,\n  Quot.sound]"
        self.assertEqual(check_axioms.parse_axioms(log),
                         {"L1": {"propext", "Classical.choice", "Quot.sound"}})

    def test_no_axioms(self):
        log = "'Architecton.Temporal.D5' does not depend on any axioms"
        self.assertEqual(check_axioms.parse_axioms(log), {"D5": set()})


class Check(unittest.TestCase):
    def test_accepts_standard_axioms(self):
        self.assertEqual(check_axioms.check(full_log(), []), [])

    def test_rejects_extra_axiom(self):
        log = full_log(skip=("D1",)) + "\n'Architecton.Temporal.D1' depends on axioms: [propext, Lean.ofReduceBool]"
        problems = check_axioms.check(log, [])
        self.assertTrue(any("Lean.ofReduceBool" in p for p in problems), problems)

    def test_missing_required(self):
        problems = check_axioms.check(full_log(skip=("D4b",)), [])
        self.assertTrue(any("D4b" in p for p in problems), problems)

    def test_scan_flags_sorry_and_native_decide(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "Bad.lean"
            f.write_text("theorem a : True := by sorry\ntheorem b : 1 = 1 := by native_decide\n",
                         encoding="utf-8")
            self.assertEqual(len(check_axioms.scan_sources([f])), 2)

    def test_scan_flags_axiom_declaration(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "Bad.lean"
            f.write_text("axiom cheat : False\n", encoding="utf-8")
            self.assertEqual(len(check_axioms.scan_sources([f])), 1)

    def test_scan_ignores_words_in_comments(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "Ok.lean"
            f.write_text("/-! No `sorry`, no `axiom`. -/\ntheorem a : True := trivial\n",
                         encoding="utf-8")
            self.assertEqual(check_axioms.scan_sources([f]), [])


if __name__ == "__main__":
    unittest.main()
