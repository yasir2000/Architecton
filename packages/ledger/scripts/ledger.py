#!/usr/bin/env python3
"""ledger: Architecton's trusted evidence ledger.

Each run of a check becomes an ENTRY: a canonical JSON record of the check's
command, the SHA-256 of every input file, the entries it depends on, the result
and the validator who ran it. The entry's ID is the SHA-256 of its bytes
(content addressing), and the validator signs those bytes with an SSH key
(`ssh-keygen -Y sign`). Entries are never edited; a bad one is REVOKED by a
signed revocation record.

An entry is VALID when (formal/Ledger.lean, `Valid`):
  * its file name equals its hash and its signature verifies against
    `allowed_signers` for the validator it names;
  * its result is `pass` and it is not revoked by a validly signed revocation;
  * its check definition and every input file are unchanged since it ran;
  * every entry it depends on is valid.
Blocking an entry therefore invalidates exactly its dependents
(`valid_blockMore_iff`); `plan` lists them, and `run` re-runs only them.

Commands (run from anywhere; paths are relative to the repository root):
  ledger.py plan                     which checks lack valid evidence, and why
  ledger.py run [--force] [CHECK...] run checks lacking valid evidence; sign entries
  ledger.py verify [CHECK...]        exit 1 unless every (named) check has valid evidence
  ledger.py revoke ENTRY --reason R  sign a revocation of ENTRY
  ledger.py show ENTRY               print an entry and its validity

Signing needs --key/--principal or ARCHITECTON_EVIDENCE_KEY and
ARCHITECTON_EVIDENCE_PRINCIPAL. Verification needs only allowed_signers.
This script is tested, not formally verified.
"""
import argparse
import datetime
import glob
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import time
from pathlib import Path

LEDGER_VERSION = "1.0.0"
NAMESPACE = "architecton-evidence"
REPO = Path(__file__).resolve().parents[3]


class LedgerError(Exception):
    pass


# ---------------------------------------------------------------- basics


def canonical(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n").encode("utf-8")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def file_hash(path):
    """Text files hash with LF endings, so Windows and Linux checkouts agree."""
    data = path.read_bytes()
    if b"\x00" not in data[:8192]:
        data = data.replace(b"\r\n", b"\n")
    return sha256(data)


def now():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------- signatures


def ssh_keygen():
    exe = shutil.which("ssh-keygen")
    if not exe:
        raise LedgerError("ssh-keygen not found; it is needed to sign and verify evidence")
    return exe


def sign(data, key, principal_unused=None):
    """Return an SSH signature over `data`, made with private key file `key`."""
    key = Path(key)
    if not key.is_file():
        raise LedgerError(f"signing key not found: {key}")
    proc = subprocess.run([ssh_keygen(), "-Y", "sign", "-q", "-f", str(key), "-n", NAMESPACE],
                          input=data, capture_output=True)
    if proc.returncode != 0:
        raise LedgerError(f"signing failed: {proc.stderr.decode(errors='replace').strip()}")
    return proc.stdout


def verify_signature(data, signature, principal, allowed_signers, scratch):
    """True iff `signature` is a valid signature by `principal` per `allowed_signers`."""
    if not allowed_signers.is_file() or not principal:
        return False
    sig_file = scratch / f"sig-{sha256(signature)[:16]}.sig"
    sig_file.write_bytes(signature)
    try:
        proc = subprocess.run(
            [ssh_keygen(), "-Y", "verify", "-f", str(allowed_signers), "-I", principal,
             "-n", NAMESPACE, "-s", str(sig_file)],
            input=data, capture_output=True)
        return proc.returncode == 0
    finally:
        sig_file.unlink(missing_ok=True)


# ---------------------------------------------------------------- checks (the DAG)


def load_checks(root, checks_file):
    try:
        spec = json.loads(checks_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        raise LedgerError(f"cannot read {checks_file}: {e}") from e
    if spec.get("ledger_version") != LEDGER_VERSION:
        raise LedgerError("unsupported ledger_version in checks file")
    checks = {}
    for c in spec.get("checks", []):
        unknown = set(c) - {"id", "argv", "cwd", "env", "inputs", "depends_on", "description"}
        if unknown:
            raise LedgerError(f"check {c.get('id')!r}: unknown keys {sorted(unknown)}")
        for k in ("id", "argv", "inputs"):
            if k not in c:
                raise LedgerError(f"check {c.get('id')!r}: missing {k!r}")
        if c["id"] in checks:
            raise LedgerError(f"duplicate check {c['id']!r}")
        c.setdefault("cwd", ".")
        c.setdefault("env", {})
        c.setdefault("depends_on", [])
        checks[c["id"]] = c
    for c in checks.values():
        for d in c["depends_on"]:
            if d not in checks:
                raise LedgerError(f"check {c['id']!r} depends on unknown check {d!r}")
    return checks, topo_order(checks)


def topo_order(checks):
    order, state = [], {}

    def visit(cid, path):
        if state.get(cid) == "done":
            return
        if state.get(cid) == "active":
            raise LedgerError("dependency cycle: " + " -> ".join(path + [cid]))
        state[cid] = "active"
        for d in checks[cid]["depends_on"]:
            visit(d, path + [cid])
        state[cid] = "done"
        order.append(cid)

    for cid in sorted(checks):
        visit(cid, [])
    return order


def expand_inputs(root, check):
    """Resolve the check's input paths/globs to {relative path: hash}."""
    out = {}
    for pattern in check["inputs"]:
        matches = sorted(glob.glob(str(root / pattern), recursive=True))
        files = [Path(m) for m in matches if Path(m).is_file()]
        if not files:
            raise LedgerError(f"check {check['id']!r}: input {pattern!r} matches no file")
        for f in files:
            rel = f.resolve().relative_to(root.resolve()).as_posix()
            out[rel] = file_hash(f)
    return out


def definition(check):
    """The parts of a check that, if changed, make old evidence stale."""
    return {"argv": check["argv"], "cwd": check["cwd"], "env": check["env"],
            "inputs": check["inputs"], "depends_on": sorted(check["depends_on"])}


# ---------------------------------------------------------------- the ledger store


class Ledger:
    def __init__(self, root=REPO, ledger_dir=None, checks_file=None, allowed_signers=None):
        self.root = Path(root)
        self.dir = Path(ledger_dir) if ledger_dir else self.root / "evidence" / "ledger"
        self.checks_file = Path(checks_file) if checks_file else self.root / "evidence" / "checks.json"
        self.allowed = Path(allowed_signers) if allowed_signers else self.root / "evidence" / "allowed_signers"
        self.checks, self.order = load_checks(self.root, self.checks_file)
        self.scratch = self.dir / ".scratch"

    # -- storage

    def entries_dir(self):
        return self.dir / "entries"

    def revocations_dir(self):
        return self.dir / "revocations"

    def load(self):
        """Read every entry and revocation, and decide which are authentic."""
        self.scratch.mkdir(parents=True, exist_ok=True)
        self.entries, self.problems = {}, {}
        for f in sorted(self.entries_dir().glob("*.json")) if self.entries_dir().is_dir() else []:
            data = f.read_bytes()
            eid = f.stem
            sig = f.with_suffix(".json.sig")
            try:
                entry = json.loads(data)
            except json.JSONDecodeError:
                self.problems[eid] = "not valid JSON"
                continue
            self.entries[eid] = entry
            if sha256(data) != eid:
                self.problems[eid] = "content does not match its ID (tampered or renamed)"
            elif data != canonical(entry):
                self.problems[eid] = "not in canonical form"
            elif not sig.is_file():
                self.problems[eid] = "unsigned"
            elif not verify_signature(data, sig.read_bytes(), entry.get("validator"),
                                      self.allowed, self.scratch):
                self.problems[eid] = f"signature does not verify for {entry.get('validator')!r}"
        self.revoked = {}
        for f in sorted(self.revocations_dir().glob("*.json")) if self.revocations_dir().is_dir() else []:
            data = f.read_bytes()
            sig = f.with_suffix(".json.sig")
            try:
                rec = json.loads(data)
            except json.JSONDecodeError:
                continue
            if (sha256(data) == f.stem and sig.is_file()
                    and verify_signature(data, sig.read_bytes(), rec.get("validator"),
                                         self.allowed, self.scratch)):
                self.revoked.setdefault(rec["revokes"], rec)
        shutil.rmtree(self.scratch, ignore_errors=True)

    def write_signed(self, folder, record, key):
        data = canonical(record)
        rid = sha256(data)
        folder.mkdir(parents=True, exist_ok=True)
        path = folder / f"{rid}.json"
        if path.exists():
            raise LedgerError(f"record {rid} already exists; entries are immutable")
        signature = sign(data, key)
        path.write_bytes(data)
        path.with_suffix(".json.sig").write_bytes(signature)
        return rid

    # -- validity (formal/Ledger.lean)

    def blocked_reason(self, eid):
        """Why entry `eid` is blocked by itself (not via dependencies), or None."""
        if eid not in self.entries:
            return "missing"
        if eid in self.problems:
            return self.problems[eid]
        e = self.entries[eid]
        if eid in self.revoked:
            return f"revoked: {self.revoked[eid].get('reason', '')}"
        if e.get("result") != "pass":
            return f"result is {e.get('result')!r}"
        check = self.checks.get(e.get("check"))
        if check is None:
            return f"check {e.get('check')!r} no longer defined"
        if e.get("definition") != definition(check):
            return "check definition changed"
        try:
            current = expand_inputs(self.root, check)
        except LedgerError as err:
            return str(err)
        if current != e.get("inputs"):
            changed = sorted(set(current.items()) ^ set(e.get("inputs", {}).items()))
            return "inputs changed: " + ", ".join(sorted({p for p, _ in changed}))
        if set(e.get("depends_on", {})) != set(check["depends_on"]):
            return "dependency set changed"
        return None

    def validity(self):
        """Map each entry ID to None (valid) or the reason it is invalid."""
        memo = {}

        def go(eid, stack):
            if eid in memo:
                return memo[eid]
            if eid in stack:
                return "dependency cycle"
            reason = self.blocked_reason(eid)
            if reason is None:
                for dcheck, did in sorted(self.entries[eid].get("depends_on", {}).items()):
                    if self.entries.get(did, {}).get("check") != dcheck:
                        reason = f"dependency {dcheck} points at a different check"
                        break
                    r = go(did, stack | {eid})
                    if r is not None:
                        reason = f"dependency {dcheck} invalid ({r})"
                        break
            memo[eid] = reason
            return reason

        return {eid: go(eid, frozenset()) for eid in self.entries}

    def current(self):
        """For each check: (latest valid entry ID or None, reason if none)."""
        valid = self.validity()
        out = {}
        for cid in self.order:
            cands = [eid for eid, e in self.entries.items() if e.get("check") == cid]
            good = [eid for eid in cands if valid[eid] is None]
            if good:
                out[cid] = (max(good, key=lambda i: (self.entries[i].get("finished_at", ""), i)), None)
            elif cands:
                latest = max(cands, key=lambda i: (self.entries[i].get("finished_at", ""), i))
                out[cid] = (None, valid[latest])
            else:
                out[cid] = (None, "never run")
        return out

    # -- running

    def run_check(self, cid, dep_entries, key, principal):
        check = self.checks[cid]
        inputs = expand_inputs(self.root, check)
        argv = [sys.executable if a == "python3" else a for a in check["argv"]]
        env = dict(os.environ)
        for k, v in check["env"].items():
            env[k] = os.pathsep.join(str((self.root / p).resolve()) for p in v) if isinstance(v, list) else v
        started = now()
        t0 = time.monotonic()
        try:
            proc = subprocess.run(argv, cwd=self.root / check["cwd"], env=env, capture_output=True)
            code, out = proc.returncode, proc.stdout + proc.stderr
        except OSError as e:
            code, out = 127, str(e).encode()
        entry = {
            "ledger_version": LEDGER_VERSION,
            "check": cid,
            "definition": definition(check),
            "inputs": inputs,
            "depends_on": dep_entries,
            "result": "pass" if code == 0 else "fail",
            "exit_code": code,
            "output_sha256": sha256(out),
            "output_tail": out.decode("utf-8", errors="replace")[-2000:],
            "validator": principal,
            "platform": f"{platform.system()} {platform.machine()} / Python {platform.python_version()}",
            "started_at": started,
            "finished_at": now(),
            "duration_s": round(time.monotonic() - t0, 3),
        }
        return self.write_signed(self.entries_dir(), entry, key), entry["result"]

    def run(self, key, principal, only=None, force=False, log=print):
        if not principal:
            raise LedgerError("a validator principal is required to sign evidence")
        wanted = set(self.order)
        if only:
            unknown = set(only) - wanted
            if unknown:
                raise LedgerError(f"unknown checks {sorted(unknown)}")
            wanted = set()
            stack = list(only)
            while stack:  # a check needs its dependencies' evidence too
                c = stack.pop()
                if c not in wanted:
                    wanted.add(c)
                    stack.extend(self.checks[c]["depends_on"])
        self.load()
        status = self.current()
        summary = {"reused": [], "ran": [], "failed": [], "skipped": []}
        for cid in self.order:
            if cid not in wanted:
                continue
            existing, _ = status[cid]
            if existing and not force:
                summary["reused"].append(cid)
                log(f"reuse  {cid}  {existing[:12]}")
                continue
            deps = {d: status[d][0] for d in self.checks[cid]["depends_on"]}
            if any(v is None for v in deps.values()):
                summary["skipped"].append(cid)
                log(f"skip   {cid}  (a dependency has no valid evidence)")
                continue
            eid, result = self.run_check(cid, deps, key, principal)
            self.load()
            status = self.current()
            summary["ran" if result == "pass" else "failed"].append(cid)
            log(f"{'ran   ' if result == 'pass' else 'FAILED'} {cid}  {eid[:12]}")
        return summary

    def revoke(self, entry_id, reason, key, principal):
        if not reason.strip():
            raise LedgerError("a revocation needs a reason")
        self.load()
        if entry_id not in self.entries:
            raise LedgerError(f"no entry {entry_id}")
        record = {"ledger_version": LEDGER_VERSION, "revokes": entry_id, "reason": reason,
                  "validator": principal, "at": now()}
        return self.write_signed(self.revocations_dir(), record, key)


# ---------------------------------------------------------------- CLI


def signing_args(args):
    key = args.key or os.environ.get("ARCHITECTON_EVIDENCE_KEY")
    principal = args.principal or os.environ.get("ARCHITECTON_EVIDENCE_PRINCIPAL")
    if not key or not principal:
        raise LedgerError("signing needs --key and --principal "
                          "(or ARCHITECTON_EVIDENCE_KEY and ARCHITECTON_EVIDENCE_PRINCIPAL)")
    return key, principal


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=str(REPO))
    ap.add_argument("--ledger")
    ap.add_argument("--checks")
    ap.add_argument("--allowed-signers")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("plan")
    r = sub.add_parser("run")
    r.add_argument("checks", nargs="*")
    r.add_argument("--force", action="store_true")
    v = sub.add_parser("verify")
    v.add_argument("checks", nargs="*")
    k = sub.add_parser("revoke")
    k.add_argument("entry")
    k.add_argument("--reason", required=True)
    s = sub.add_parser("show")
    s.add_argument("entry")
    for p in (r, k):
        p.add_argument("--key")
        p.add_argument("--principal")
    args = ap.parse_args(argv)
    try:
        L = Ledger(args.root, args.ledger, args.checks, args.allowed_signers)
        if args.cmd == "run":
            key, principal = signing_args(args)
            summary = L.run(key, principal, args.checks or None, args.force)
            print(" ".join(f"{k}={len(v)}" for k, v in summary.items()))
            return 1 if summary["failed"] or summary["skipped"] else 0
        if args.cmd == "revoke":
            key, principal = signing_args(args)
            print(f"revoked {args.entry} by {L.revoke(args.entry, args.reason, key, principal)}")
            return 0
        L.load()
        if args.cmd == "show":
            matches = [e for e in L.entries if e.startswith(args.entry)]
            if len(matches) != 1:
                raise LedgerError(f"{len(matches)} entries match {args.entry!r}")
            reason = L.validity()[matches[0]]
            print(json.dumps(L.entries[matches[0]], indent=2))
            print("VALID" if reason is None else f"INVALID: {reason}")
            return 0
        status = L.current()
        names = args.checks if args.cmd == "verify" and args.checks else L.order
        missing = [c for c in names if c not in status]
        if missing:
            raise LedgerError(f"unknown checks {missing}")
        bad = 0
        for cid in names:
            eid, reason = status[cid]
            if eid:
                e = L.entries[eid]
                print(f"ok     {cid:<28} {eid[:12]}  {e['validator']}  {e['finished_at']}")
            else:
                bad += 1
                print(f"needed {cid:<28} {reason}")
        if args.cmd == "verify":
            print("PASS: all checks have valid evidence" if not bad else f"FAIL: {bad} check(s) lack valid evidence")
        return 1 if (bad and args.cmd == "verify") else 0
    except LedgerError as e:
        print(f"ERROR: {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
