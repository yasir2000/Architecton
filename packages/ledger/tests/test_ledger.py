"""Tests for ledger.py. Each test builds a throwaway repository with its own
checks and freshly generated SSH keys.

    python3 -m unittest discover -s packages/ledger/tests -v
"""
import json
import random
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import ledger  # noqa: E402

HAVE_SSH = shutil.which("ssh-keygen") is not None


def keypair(folder, name):
    key = folder / name
    subprocess.run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", name, "-f", str(key)], check=True)
    return key


# A check that records each execution, so tests can tell reuse from re-runs.
def counting(name, inputs, deps=(), fail=False):
    code = (f"open('runs.log','a').write('{name}\\n')" + ("; raise SystemExit(3)" if fail else ""))
    return {"id": name, "argv": ["python3", "-c", code], "inputs": list(inputs), "depends_on": list(deps)}


@unittest.skipUnless(HAVE_SSH, "ssh-keygen not available")
class LedgerTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.root = self.tmp / "repo"
        (self.root / "evidence").mkdir(parents=True)
        for name in ("a.txt", "b.txt", "c.txt"):
            (self.root / name).write_text(f"{name}\n", encoding="utf-8")
        self.key = keypair(self.tmp, "ci")
        self.other = keypair(self.tmp, "mallory")
        # Only `ci@example` is trusted.
        pub = self.key.with_suffix(".pub").read_text().strip()
        (self.root / "evidence/allowed_signers").write_text(f"ci@example {pub}\n")
        # DAG:  base(a) <- mid(b) <- top(c);  side(c) is independent.
        self.write_checks([
            counting("base", ["a.txt"]),
            counting("mid", ["b.txt"], ["base"]),
            counting("top", ["c.txt"], ["mid"]),
            counting("side", ["c.txt"]),
        ])

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def write_checks(self, checks):
        (self.root / "evidence/checks.json").write_text(
            json.dumps({"ledger_version": ledger.LEDGER_VERSION, "checks": checks}), encoding="utf-8")

    def L(self):
        return ledger.Ledger(self.root)

    def run_all(self, **kw):
        return self.L().run(str(self.key), "ci@example", log=lambda *_: None, **kw)

    def runs(self):
        log = self.root / "runs.log"
        return log.read_text().split() if log.exists() else []

    def status(self):
        L = self.L()
        L.load()
        return {c: (eid is not None, reason) for c, (eid, reason) in L.current().items()}

    def valid_checks(self):
        return {c for c, (ok, _) in self.status().items() if ok}

    def entry_of(self, check):
        L = self.L()
        L.load()
        return L.current()[check][0]

    # -- basics

    def test_run_then_verify(self):
        self.assertEqual(sorted(self.run_all()["ran"]), ["base", "mid", "side", "top"])
        self.assertEqual(self.valid_checks(), {"base", "mid", "side", "top"})
        self.assertEqual(ledger.main(["--root", str(self.root), "verify"]), 0)

    def test_second_run_reuses_everything(self):
        self.run_all()
        before = self.runs()
        summary = self.run_all()
        self.assertEqual(sorted(summary["reused"]), ["base", "mid", "side", "top"])
        self.assertEqual(self.runs(), before, "nothing should re-execute")

    def test_entries_are_content_addressed_and_signed(self):
        self.run_all()
        for f in (self.root / "evidence/ledger/entries").glob("*.json"):
            self.assertEqual(ledger.sha256(f.read_bytes()), f.stem)
            self.assertTrue(f.with_suffix(".json.sig").is_file())

    def test_entries_are_immutable(self):
        L = self.L()
        record = {"x": 1}
        L.write_signed(L.entries_dir(), record, str(self.key))
        with self.assertRaises(ledger.LedgerError):
            L.write_signed(L.entries_dir(), record, str(self.key))

    # -- scoped re-verification

    def test_changed_input_invalidates_exactly_the_dependents(self):
        self.run_all()
        (self.root / "b.txt").write_text("changed\n", encoding="utf-8")
        st = self.status()
        self.assertEqual(self.valid_checks(), {"base", "side"})
        self.assertIn("inputs changed: b.txt", st["mid"][1])
        self.assertIn("dependency mid invalid", self.L_reason("top"))
        before = len(self.runs())
        summary = self.run_all()
        self.assertEqual(sorted(summary["ran"]), ["mid", "top"])
        self.assertEqual(sorted(summary["reused"]), ["base", "side"])
        self.assertEqual(self.runs()[before:], ["mid", "top"])

    def L_reason(self, check):
        L = self.L()
        L.load()
        return L.validity()[[e for e, x in L.entries.items() if x["check"] == check][0]]

    def test_crlf_change_is_not_a_change(self):
        self.run_all()
        (self.root / "a.txt").write_bytes(b"a.txt\r\n")
        self.assertEqual(self.valid_checks(), {"base", "mid", "side", "top"})

    def test_changed_definition_is_stale(self):
        self.run_all()
        checks = json.loads((self.root / "evidence/checks.json").read_text())
        checks["checks"][3]["argv"] = ["python3", "-c", "pass"]
        (self.root / "evidence/checks.json").write_text(json.dumps(checks))
        self.assertEqual(self.status()["side"], (False, "check definition changed"))

    # -- revocation

    def test_revocation_invalidates_exactly_the_dependents(self):
        self.run_all()
        self.L().revoke(self.entry_of("mid"), "flaky runner", str(self.key), "ci@example")
        self.assertEqual(self.valid_checks(), {"base", "side"})
        self.assertIn("revoked: flaky runner", self.status()["mid"][1])

    def test_forged_revocation_is_ignored(self):
        self.run_all()
        self.L().revoke(self.entry_of("base"), "forged", str(self.other), "mallory@example")
        self.assertEqual(self.valid_checks(), {"base", "mid", "side", "top"})

    # -- authenticity

    def test_tampered_entry_is_rejected(self):
        self.run_all()
        eid = self.entry_of("side")
        f = self.root / f"evidence/ledger/entries/{eid}.json"
        f.write_bytes(f.read_bytes().replace(b'"exit_code":0', b'"exit_code":1'))
        self.assertIn("tampered", self.status()["side"][1])

    def test_untrusted_signer_is_rejected(self):
        self.L().run(str(self.other), "mallory@example", log=lambda *_: None)
        self.assertEqual(self.valid_checks(), set())
        self.assertIn("signature does not verify", self.status()["base"][1])

    def test_signature_bound_to_principal(self):
        # A trusted key cannot sign as someone else.
        self.L().run(str(self.key), "admin@example", log=lambda *_: None)
        self.assertEqual(self.valid_checks(), set())

    def test_unsigned_entry_is_rejected(self):
        self.run_all()
        eid = self.entry_of("side")
        (self.root / f"evidence/ledger/entries/{eid}.json.sig").unlink()
        self.assertEqual(self.status()["side"], (False, "unsigned"))

    # -- failures and the DAG

    def test_failing_check_blocks_dependents(self):
        self.write_checks([
            counting("base", ["a.txt"], fail=True),
            counting("mid", ["b.txt"], ["base"]),
            counting("side", ["c.txt"]),
        ])
        summary = self.run_all()
        self.assertEqual(summary["failed"], ["base"])
        self.assertEqual(summary["skipped"], ["mid"])
        self.assertNotIn("mid", self.runs())
        self.assertEqual(self.valid_checks(), {"side"})

    def test_run_selected_check_brings_dependencies(self):
        summary = self.L().run(str(self.key), "ci@example", only=["mid"], log=lambda *_: None)
        self.assertEqual(sorted(summary["ran"]), ["base", "mid"])

    def test_cycle_rejected(self):
        self.write_checks([counting("x", ["a.txt"], ["y"]), counting("y", ["b.txt"], ["x"])])
        with self.assertRaises(ledger.LedgerError):
            self.L()

    def test_missing_input_rejected(self):
        self.write_checks([counting("x", ["nope.txt"])])
        summary = None
        with self.assertRaises(ledger.LedgerError):
            summary = self.run_all()
        self.assertIsNone(summary)


class ScopeProperty(unittest.TestCase):
    """The Lean theorem `revoke_scope`, tested on the Python rule: on random
    DAGs, revoking entry r invalidates exactly the entries that reach r."""

    def test_random_dags(self):
        rng = random.Random(0)
        for _ in range(300):
            n = rng.randint(1, 9)
            deps = {i: [j for j in range(i) if rng.random() < 0.3] for i in range(n)}
            blocked = {i for i in range(n) if rng.random() < 0.15}
            r = rng.randrange(n)

            def valid(b):
                memo = {}
                def go(i):
                    if i not in memo:
                        memo[i] = i not in b and all(go(d) for d in deps[i])
                    return memo[i]
                return {i for i in range(n) if go(i)}

            def reaches(i, t):
                return i == t or any(reaches(d, t) for d in deps[i])

            before, after = valid(blocked), valid(blocked | {r})
            self.assertEqual(after, {i for i in before if not reaches(i, r)})


if __name__ == "__main__":
    unittest.main()
