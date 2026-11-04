"""Tests for designc.py. Each test serves one modified file in memory (the real
files are never touched) and expects a specific error.

    python3 -m unittest discover -s packages/design/tests -v
"""
import json
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import designc  # noqa: E402

LIFECYCLE = designc.REPO / "packages/lifecycle/design/conformance.json"
DRIVERPASS = designc.REPO / "examples/driverpass/design/conformance.json"
STATE = "packages/lifecycle/design/phase-state-machine.puml"
SEQ = "examples/driverpass/design/sequence.puml"
CLASSES = "examples/driverpass/design/domain.puml"
ARCH = "examples/driverpass/design/architecture.json"
SERVICE = "examples/driverpass/backend/src/service.rs"
TX_LEAN = "examples/driverpass/formal/Transactions.lean"
DOMAIN_RS = "examples/driverpass/backend/src/domain.rs"

real_read = designc.read


def spec(path, kind):
    return next(c for c in json.loads(path.read_text(encoding="utf-8"))["checks"] if c["kind"] == kind)


class Base(unittest.TestCase):
    def errors(self, kind, spec_file, overrides):
        """Run one check with some files replaced: {path: new_text or fn(old) -> new}."""
        def fake_read(rel):
            text = real_read(rel)
            if rel in overrides:
                o = overrides[rel]
                return o(text) if callable(o) else o
            return text
        errs = []
        with mock.patch.object(designc, "read", fake_read):
            try:
                designc.CHECKS[kind](spec(spec_file, kind), errs)
            except designc.DesignError as e:
                errs.append(str(e))
        return errs

    def expect(self, kind, spec_file, overrides, fragment):
        errs = self.errors(kind, spec_file, overrides)
        self.assertTrue(any(fragment in e for e in errs), f"wanted {fragment!r}, got {errs}")

    def replace(self, old, new):
        def f(text):
            self.assertIn(old, text, "test setup: text to replace not found")
            return text.replace(old, new, 1)
        return f


class RealModelsPass(Base):
    def test_lifecycle(self):
        self.assertEqual(designc.run_spec(LIFECYCLE)[1], [])

    def test_driverpass(self):
        self.assertEqual(designc.run_spec(DRIVERPASS)[1], [])

    def test_generated_lean_in_sync(self):
        self.assertEqual(designc.main(["lean", "--check", str(LIFECYCLE)]), 0)


class StateMachine(Base):
    def s(self, old, new, fragment):
        self.expect("state", LIFECYCLE, {STATE: self.replace(old, new)}, fragment)

    def test_weakened_gate(self):
        self.s("conformancePassed && artifactBuilt]", "conformancePassed]", "promote guard")

    def test_skipped_phase(self):
        self.s("Elaboration --> Construction : promote", "Elaboration --> Transition : promote",
               "policy says construction")

    def test_missing_iterate_loop(self):
        self.s("Construction --> Construction : iterate / iteration++\n", "", "needs an 'iterate' self-loop")

    def test_nondeterminism(self):
        self.s("Inception --> Inception : iterate / iteration++",
               "Inception --> Inception : iterate / iteration++\nInception --> Elaboration : iterate",
               "nondeterministic")

    def test_unknown_event(self):
        self.s("Transition --> Transition : iterate", "Transition --> Transition : celebrate", "unknown event")

    def test_unknown_evidence(self):
        self.s("[requirementsReviewed &&", "[vibesChecked &&", "unknown evidence 'vibesChecked'")

    def test_unreachable_state(self):
        self.s("Inception --> Elaboration : promote [requirementsReviewed && traceabilityReviewed]\n", "",
               "unreachable")

    def test_two_initial_states(self):
        self.s("[*] --> Inception", "[*] --> Inception\n[*] --> Elaboration", "exactly one initial")

    def test_terminal_phase_cannot_promote(self):
        self.s("Transition --> Transition : iterate / iteration++",
               "Transition --> Transition : iterate / iteration++\nTransition --> Inception : promote",
               "terminal in the policy")

    def test_outside_subset(self):
        self.s("[*] --> Inception", "[*] --> Inception\nstate Inception : entry / audit", "outside the state-machine subset")


class Sequence(Base):
    def test_diagram_steps_out_of_order(self):
        def swap(t):
            return t.replace("API -> DB: INSERT audit decision\nAPI -> DB: COMMIT",
                             "API -> DB: COMMIT\nAPI -> DB: INSERT audit decision")
        self.expect("sequence", DRIVERPASS, {SEQ: swap}, "missing or out of order")

    def test_insert_outside_alt(self):
        def move(t):
            t = t.replace("  API -> DB: INSERT allocation\n", "")
            return t.replace("API -> DB: Read roster", "API -> DB: Read roster\nAPI -> DB: INSERT allocation")
        self.expect("sequence", DRIVERPASS, {SEQ: move}, "missing or out of order")

    def test_insert_under_wrong_condition(self):
        self.expect("sequence", DRIVERPASS, {SEQ: self.replace("alt accepted", "alt rejected")},
                    "drawn under ['rejected']")

    def test_code_audits_before_inserting(self):
        def swap(t):
            a = t.index("    if decision == Decision::Accepted {")
            b = t.index("    inject(fault, Fault::AfterAllocationInsert)?;")
            c = t.index("    inject(fault, Fault::AfterAuditInsert)?;")
            audit = t[t.index("    // SR-003", b):c]
            return t[:a] + audit + t[a:b] + t[b:].replace(audit, "", 1)
        self.expect("sequence", DRIVERPASS, {SERVICE: swap}, "order differs")

    def test_lean_model_out_of_order(self):
        def swap(t):
            return t.replace("let db1 := if r.2 = .accepted then { db with allocations := (i, slot) :: db.allocations } else db",
                             "let db1 := { db with audit := (i, slot, r.2) :: db.audit }")
        self.expect("sequence", DRIVERPASS, {TX_LEAN: swap}, "Transactions.lean")

    def test_undeclared_participant(self):
        self.expect("sequence", DRIVERPASS, {SEQ: self.replace("API -> DB: COMMIT", "API -> Cache: COMMIT")},
                    "undeclared participant")

    def test_unbalanced_alt(self):
        self.expect("sequence", DRIVERPASS, {SEQ: self.replace("\nend\n", "\n")}, "alt never closed")


class Classes(Base):
    def test_enum_literal_renamed(self):
        self.expect("class", DRIVERPASS, {CLASSES: self.replace("  duplicate\n", "  clash\n")},
                    "literals")

    def test_field_type_mismatch(self):
        self.expect("class", DRIVERPASS, {CLASSES: self.replace("+offDuty: Boolean", "+offDuty: Integer")},
                    "does not match IR offDuty : Bool")

    def test_unmapped_field(self):
        self.expect("class", DRIVERPASS,
                    {CLASSES: self.replace("+slots: List<Integer>", "+slots: List<Integer>\n  +region: Integer")},
                    "region has no IR counterpart")

    def test_rust_variant_missing(self):
        self.expect("class", DRIVERPASS, {DOMAIN_RS: self.replace("    Duplicate,\n", "")}, "serializes as")


class ArchiMate(Base):
    def model(self, change):
        def f(text):
            m = json.loads(text)
            change(m)
            return json.dumps(m)
        return {ARCH: f}

    def test_disallowed_relationship(self):
        self.expect("archimate", DRIVERPASS,
                    self.model(lambda m: m["relationships"].append({"type": "realization", "from": "DO-roster", "to": "G0"})),
                    "not in the supported ArchiMate subset")

    def test_unknown_type(self):
        self.expect("archimate", DRIVERPASS,
                    self.model(lambda m: m["elements"].append({"id": "X", "type": "Microservice", "trace": []})),
                    "unknown or unsupported type")

    def test_broken_trace(self):
        def f(m):
            m["elements"][-1]["trace"][0]["anchor"] = "not in the Dockerfile"
        self.expect("archimate", DRIVERPASS, self.model(f), "not in examples/driverpass/infra/Dockerfile")

    def test_core_element_needs_trace(self):
        self.expect("archimate", DRIVERPASS,
                    self.model(lambda m: m["elements"].append({"id": "AS-x", "type": "ApplicationService"})),
                    "without a trace")

    def test_requirement_unrealized(self):
        self.expect("archimate", DRIVERPASS,
                    self.model(lambda m: m.update(relationships=[r for r in m["relationships"]
                                                                 if not (r["to"] == "SR-003")])),
                    "SR-003 is realized by no element")

    def test_ir_requirement_missing(self):
        self.expect("archimate", DRIVERPASS,
                    self.model(lambda m: m.update(elements=[e for e in m["elements"] if e["id"] != "BR-002"],
                                                  relationships=[r for r in m["relationships"]
                                                                 if "BR-002" not in (r["from"], r["to"])])),
                    "IR requirement BR-002 has no ArchiMate element")


if __name__ == "__main__":
    unittest.main()
