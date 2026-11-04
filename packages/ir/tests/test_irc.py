"""Unit tests for irc.py. Run from the repository root or anywhere:

    python3 -m unittest discover -s packages/ir/tests -v
"""
import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "scripts"))
import irc  # noqa: E402

DRIVERPASS = irc.REPO / "examples/driverpass/ir/driverpass.ir.json"


def base():
    return irc.load(DRIVERPASS)


class Valid(unittest.TestCase):
    def test_driverpass_checks(self):
        self.assertEqual(irc.check(base()), [])

    def test_digest_ignores_key_order_and_layout(self):
        ir = base()
        shuffled = json.loads(json.dumps(ir, sort_keys=True, indent=7))
        self.assertEqual(irc.digest(ir), irc.digest(shuffled))

    def test_crlf_and_lf_hash_alike(self):
        self.assertEqual(irc.artifact_hash(b"a\r\nb\r\n"), irc.artifact_hash(b"a\nb\n"))

    def test_binary_hash_is_raw(self):
        self.assertNotEqual(irc.artifact_hash(b"\x00a\r\n"), irc.artifact_hash(b"\x00a\n"))

    def test_generated_lean_in_sync(self):
        rc = irc.main(["lean", str(DRIVERPASS), "--check",
                       "--out", str(DRIVERPASS.with_name("DriverPassIR.lean")),
                       "--ident", "driverPass"])
        self.assertEqual(rc, 0)


class Rejects(unittest.TestCase):
    """Each test breaks one thing and expects a specific error."""

    def expect(self, ir, fragment, check_files=True):
        errors = irc.check(ir, check_files)
        self.assertTrue(any(fragment in e for e in errors),
                        f"expected an error containing {fragment!r}, got {errors}")

    def transition(self, ir):
        return ir["transitions"][0]

    def test_unknown_key(self):
        ir = base()
        ir["goals"][0]["owner"] = "me"
        self.expect(ir, "unknown keys ['owner']")

    def test_unknown_version(self):
        ir = base()
        ir["ir_version"] = "2.0.0"
        self.expect(ir, "unsupported ir_version")

    def test_duplicate_identifier(self):
        ir = base()
        ir["risks"][0]["id"] = "BR-001"
        self.expect(ir, "duplicate identifier 'BR-001'")

    def test_goal_cycle(self):
        ir = base()
        ir["goals"][0]["parent"] = "G1"
        self.expect(ir, "cycle")

    def test_unknown_parent(self):
        ir = base()
        ir["goals"][1]["parent"] = "G99"
        self.expect(ir, "unknown parent goal 'G99'")

    def test_requirement_without_goal(self):
        ir = base()
        ir["requirements"][0]["goals"] = []
        self.expect(ir, "at least one goal")

    def test_unknown_requirement_kind(self):
        ir = base()
        ir["requirements"][0]["kind"] = "wish"
        self.expect(ir, "unknown kind 'wish'")

    def test_mitigated_risk_needs_requirement(self):
        ir = base()
        ir["risks"][0]["mitigated_by"] = []
        self.expect(ir, "must name its mitigating requirements")

    def test_risk_unknown_mitigation(self):
        ir = base()
        ir["risks"][0]["mitigated_by"] = ["BR-999"]
        self.expect(ir, "unknown mitigating requirement 'BR-999'")

    def test_guard_not_boolean(self):
        ir = base()
        self.transition(ir)["guards"][0]["when"] = {"param": "slot"}
        self.expect(ir, "guard has type nat, expected bool")

    def test_operator_argument_type(self):
        ir = base()
        self.transition(ir)["guards"][1]["when"] = {"contains": [{"param": "slot"}, {"var": "slots"}]}
        self.expect(ir, "contains argument 0 has type nat, expected natList")

    def test_unknown_operator(self):
        ir = base()
        self.transition(ir)["guards"][0]["when"] = {"xor": [{"var": "offDuty"}, {"bool": True}]}
        self.expect(ir, "unknown operator 'xor'")

    def test_unknown_variable(self):
        ir = base()
        self.transition(ir)["guards"][0]["when"] = {"var": "onLeave"}
        self.expect(ir, "unknown state variable 'onLeave'")

    def test_effect_type_mismatch(self):
        ir = base()
        self.transition(ir)["otherwise"]["effect"][0]["value"] = {"bool": True}
        self.expect(ir, "value has type bool, but slots is natList")

    def test_effect_double_write(self):
        ir = base()
        eff = self.transition(ir)["otherwise"]["effect"]
        eff.append(copy.deepcopy(eff[0]))
        self.expect(ir, "assigns 'slots' twice")

    def test_invariant_cannot_use_parameters(self):
        ir = base()
        ir["invariants"][0]["body"] = {"contains": [{"var": "slots"}, {"param": "slot"}]}
        self.expect(ir, "unknown parameter 'slot'")

    def test_duplicate_outcomes(self):
        ir = base()
        self.transition(ir)["guards"][1]["outcome"] = "off_duty"
        self.expect(ir, "outcomes must be distinct")

    def test_negative_nat_literal(self):
        ir = base()
        self.transition(ir)["guards"][0]["when"] = {"eq_nat": [{"param": "slot"}, {"nat": -1}]}
        self.expect(ir, "non-negative integer")

    def test_unknown_anchor_role(self):
        ir = base()
        ir["goals"][0]["provenance"][0]["role"] = "vibes"
        self.expect(ir, "unknown role 'vibes'")

    def test_anchor_unknown_artifact(self):
        ir = base()
        ir["goals"][0]["provenance"][0]["artifact"] = "ART-NOPE"
        self.expect(ir, "unknown artifact 'ART-NOPE'")

    def test_anchor_text_missing(self):
        ir = base()
        ir["requirements"][0]["provenance"][1]["anchor"] = "theorem does_not_exist"
        self.expect(ir, "not found in ART-LEAN-PROOFS")

    def test_anchor_in_docx_missing(self):
        ir = base()
        ir["goals"][0]["provenance"][0]["anchor"] = "text the BRD never says"
        self.expect(ir, "not found in ART-BRD")

    def test_artifact_hash_drift(self):
        ir = base()
        ir["artifacts"][1]["sha256"] = "0" * 64
        self.expect(ir, "changed since review")

    def test_missing_artifact(self):
        ir = base()
        ir["artifacts"][1]["path"] = "examples/driverpass/requirements/gone.json"
        self.expect(ir, "artifact not found")

    def test_path_escape(self):
        ir = base()
        ir["artifacts"][1]["path"] = "../outside.txt"
        self.expect(ir, "escapes the repository")

    def test_stale_generated_lean(self):
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "Stale.lean"
            out.write_text("-- stale\n", encoding="utf-8")
            rc = irc.main(["lean", str(DRIVERPASS), "--check", "--out", str(out),
                           "--ident", "driverPass"])
        self.assertEqual(rc, 1)


if __name__ == "__main__":
    unittest.main()
