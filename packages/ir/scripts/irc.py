#!/usr/bin/env python3
"""irc: checker and Lean generator for the Architecton typed artifact IR (v1).

Commands (paths in the IR are relative to the repository root):

  irc.py check FILE...             validate structure, types, references,
                                   goal acyclicity, artifact hashes and anchors
  irc.py hash --update FILE        recompute artifact hashes after REVIEW
  irc.py lean --write|--check FILE --out LEAN --ident NAME
                                   generate (or check) the Lean model of FILE
                                   with a kernel-checked well-formedness theorem
  irc.py digest FILE               print the canonical IR digest

The vocabulary is CLOSED: unknown keys, types, operators, kinds, statuses or
roles are errors. This script is tested, not formally verified. The Lean
`wellFormed` check over the generated model is an independent second check of
the structural and typing rules; hashes and anchor text are checked only here.
"""
import argparse
import hashlib
import json
import re
import sys
import zipfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
IR_VERSION = "1.0.0"
UNREADABLE = object()  # artifact could not be read; its error is already reported

TYPES = {"Bool": "bool", "Nat": "nat", "List Nat": "natList"}
REQ_KINDS = ("business", "system", "nonfunctional")
RISK_STATUSES = ("mitigated", "accepted", "open")
ROLES = ("source", "design", "proof", "implementation", "test")
ID_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_.-]*$")
NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
SHA_RE = re.compile(r"^[0-9a-f]{64}$")

# operator -> (argument types, result type); None marks a leaf handled separately.
OPS = {
    "not": (("bool",), "bool"),
    "and": (("bool", "bool"), "bool"),
    "or": (("bool", "bool"), "bool"),
    "eq_nat": (("nat", "nat"), "bool"),
    "contains": (("natList", "nat"), "bool"),
    "cons": (("nat", "natList"), "natList"),
    "nodup": (("natList",), "bool"),
}
LEAN_OP = {"not": "not", "and": "and", "or": "or", "eq_nat": "eqNat",
           "contains": "contains", "cons": "cons", "nodup": "nodup"}


class IRError(Exception):
    pass


# ---------------------------------------------------------------- loading


def load(path):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        raise IRError(f"{path}: invalid JSON: {e}") from e


def digest(ir):
    canon = json.dumps(ir, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(canon.encode("utf-8")).hexdigest()


# ---------------------------------------------------------------- artifacts


def read_artifact(rel):
    p = (REPO / rel).resolve()
    if REPO.resolve() not in p.parents:
        raise IRError(f"artifact path escapes the repository: {rel}")
    if not p.is_file():
        raise IRError(f"artifact not found: {rel}")
    return p.read_bytes()


def is_binary(data):
    return b"\x00" in data[:8192]


def artifact_hash(data):
    """SHA-256 of the artifact. Text is hashed with LF line endings so that
    Windows (CRLF) and Linux checkouts agree; binary files are hashed as-is."""
    if not is_binary(data):
        data = data.replace(b"\r\n", b"\n")
    return hashlib.sha256(data).hexdigest()


def artifact_text(rel, data):
    if rel.lower().endswith(".docx"):
        try:
            xml = zipfile.ZipFile(REPO / rel).read("word/document.xml").decode("utf-8")
        except (zipfile.BadZipFile, KeyError) as e:
            raise IRError(f"cannot read Word text of {rel}: {e}") from e
        paras = re.findall(r"<w:p[ >].*?</w:p>", xml, flags=re.S)
        return "\n".join(re.sub(r"<[^>]+>", "", p) for p in paras)
    if is_binary(data):
        return None
    return data.decode("utf-8", errors="replace")


def squash(text):
    return re.sub(r"\s+", " ", text)


# ---------------------------------------------------------------- checking


class Checker:
    def __init__(self, ir, check_files=True):
        self.ir = ir
        self.check_files = check_files
        self.errors = []

    def err(self, where, msg):
        self.errors.append(f"{where}: {msg}")

    def keys(self, where, obj, required, optional=()):
        if not isinstance(obj, dict):
            self.err(where, "expected an object")
            return False
        missing = [k for k in required if k not in obj]
        unknown = [k for k in obj if k not in required and k not in optional]
        if missing:
            self.err(where, f"missing keys {missing}")
        if unknown:
            self.err(where, f"unknown keys {unknown} (closed vocabulary)")
        return not missing

    def text(self, where, value):
        if not isinstance(value, str) or not value.strip():
            self.err(where, "statement must be a non-empty string")

    # -- expressions

    def type_of(self, where, e, state, params):
        if not isinstance(e, dict) or len(e) != 1:
            self.err(where, f"expression must be a one-key object, got {e!r}")
            return None
        (op, arg), = e.items()
        if op == "var":
            if arg not in state:
                self.err(where, f"unknown state variable {arg!r}")
                return None
            return state[arg]
        if op == "param":
            if arg not in params:
                self.err(where, f"unknown parameter {arg!r}")
                return None
            return params[arg]
        if op == "bool":
            if not isinstance(arg, bool):
                self.err(where, "bool literal must be true or false")
                return None
            return "bool"
        if op == "nat":
            if not isinstance(arg, int) or isinstance(arg, bool) or arg < 0:
                self.err(where, "nat literal must be a non-negative integer")
                return None
            return "nat"
        if op not in OPS:
            self.err(where, f"unknown operator {op!r} (closed vocabulary)")
            return None
        want, result = OPS[op]
        args = [arg] if len(want) == 1 else arg
        if not isinstance(args, list) or len(args) != len(want):
            self.err(where, f"{op} takes {len(want)} argument(s)")
            return None
        ok = True
        for i, (a, t) in enumerate(zip(args, want)):
            got = self.type_of(f"{where}.{op}[{i}]", a, state, params)
            if got is None:
                ok = False
            elif got != t:
                self.err(where, f"{op} argument {i} has type {got}, expected {t}")
                ok = False
        return result if ok else None

    # -- whole model

    def anchors(self, where, prov, artifacts):
        if not isinstance(prov, list):
            self.err(where, "provenance must be a list")
            return
        for i, a in enumerate(prov):
            w = f"{where}.provenance[{i}]"
            if not self.keys(w, a, ("artifact", "anchor", "role")):
                continue
            if a["role"] not in ROLES:
                self.err(w, f"unknown role {a['role']!r}")
            if a["artifact"] not in artifacts:
                self.err(w, f"unknown artifact {a['artifact']!r}")
                continue
            if not isinstance(a["anchor"], str) or not a["anchor"].strip():
                self.err(w, "anchor must be a non-empty string")
                continue
            text = artifacts[a["artifact"]]
            if text is UNREADABLE:
                continue
            if text is None:
                self.err(w, f"cannot check anchor in binary artifact {a['artifact']}")
            elif squash(a["anchor"]) not in text:
                self.err(w, f"anchor {a['anchor']!r} not found in {a['artifact']}")

    def run(self):
        ir = self.ir
        top = ("ir_version", "name", "artifacts", "goals", "requirements", "risks",
               "state_vars", "transitions", "invariants")
        if not self.keys("ir", ir, top):
            return self.errors
        if ir["ir_version"] != IR_VERSION:
            self.err("ir", f"unsupported ir_version {ir['ir_version']!r}")
        for k in top[2:]:
            if not isinstance(ir[k], list):
                self.err("ir", f"{k} must be a list")
                return self.errors

        ids = []

        # artifacts: hash and text used for anchors
        artifacts = {}
        for i, a in enumerate(ir["artifacts"]):
            w = f"artifacts[{i}]"
            if not self.keys(w, a, ("id", "path", "sha256")):
                continue
            ids.append((w, a["id"]))
            text = UNREADABLE
            if self.check_files:
                try:
                    data = read_artifact(a["path"])
                    actual = artifact_hash(data)
                    if not SHA_RE.match(a["sha256"] or ""):
                        self.err(w, "sha256 missing; run `irc.py hash --update` after review")
                    elif a["sha256"] != actual:
                        self.err(w, f"{a['path']} changed since review (hash {actual[:12]}..., "
                                    f"recorded {a['sha256'][:12]}...); re-review, then "
                                    "`irc.py hash --update`")
                    text = artifact_text(a["path"], data)
                    text = squash(text) if text is not None else None
                except IRError as e:
                    self.err(w, str(e))
            artifacts[a["id"]] = text

        # goals
        goal_ids = {g.get("id") for g in ir["goals"] if isinstance(g, dict)}
        parents = {}
        for i, g in enumerate(ir["goals"]):
            w = f"goals[{i}]"
            if not self.keys(w, g, ("id", "parent", "statement", "provenance")):
                continue
            ids.append((w, g["id"]))
            self.text(w, g["statement"])
            if g["parent"] is not None and g["parent"] not in goal_ids:
                self.err(w, f"unknown parent goal {g['parent']!r}")
            parents[g["id"]] = g["parent"]
            self.anchors(w, g["provenance"], artifacts)
        for gid in parents:
            seen, cur = set(), gid
            while cur is not None and cur in parents:
                if cur in seen:
                    self.err(f"goal {gid}", "goal refinement has a cycle")
                    break
                seen.add(cur)
                cur = parents[cur]

        # requirements
        req_ids = {r.get("id") for r in ir["requirements"] if isinstance(r, dict)}
        for i, r in enumerate(ir["requirements"]):
            w = f"requirements[{i}]"
            if not self.keys(w, r, ("id", "kind", "goals", "statement", "provenance")):
                continue
            ids.append((w, r["id"]))
            self.text(w, r["statement"])
            if r["kind"] not in REQ_KINDS:
                self.err(w, f"unknown kind {r['kind']!r}")
            if not isinstance(r["goals"], list) or not r["goals"]:
                self.err(w, "a requirement must refine at least one goal")
            else:
                for gid in r["goals"]:
                    if gid not in goal_ids:
                        self.err(w, f"unknown goal {gid!r}")
            self.anchors(w, r["provenance"], artifacts)

        # risks
        for i, k in enumerate(ir["risks"]):
            w = f"risks[{i}]"
            if not self.keys(w, k, ("id", "status", "mitigated_by", "statement", "provenance")):
                continue
            ids.append((w, k["id"]))
            self.text(w, k["statement"])
            if k["status"] not in RISK_STATUSES:
                self.err(w, f"unknown status {k['status']!r}")
            if not isinstance(k["mitigated_by"], list):
                self.err(w, "mitigated_by must be a list")
                continue
            for rid in k["mitigated_by"]:
                if rid not in req_ids:
                    self.err(w, f"unknown mitigating requirement {rid!r}")
            if k["status"] == "mitigated" and not k["mitigated_by"]:
                self.err(w, "a mitigated risk must name its mitigating requirements")
            self.anchors(w, k["provenance"], artifacts)

        # state variables
        state = {}
        for i, v in enumerate(ir["state_vars"]):
            w = f"state_vars[{i}]"
            if not self.keys(w, v, ("name", "type")):
                continue
            if not NAME_RE.match(str(v["name"])):
                self.err(w, f"invalid name {v['name']!r}")
            if v["type"] not in TYPES:
                self.err(w, f"unknown type {v['type']!r}; allowed {list(TYPES)}")
                continue
            if v["name"] in state:
                self.err(w, f"duplicate state variable {v['name']!r}")
            state[v["name"]] = TYPES[v["type"]]

        # transitions
        for i, t in enumerate(ir["transitions"]):
            w = f"transitions[{i}]"
            if not self.keys(w, t, ("id", "params", "guards", "otherwise")):
                continue
            ids.append((w, t["id"]))
            params = {}
            for j, p in enumerate(t["params"]):
                pw = f"{w}.params[{j}]"
                if not self.keys(pw, p, ("name", "type")):
                    continue
                if not NAME_RE.match(str(p["name"])):
                    self.err(pw, f"invalid name {p['name']!r}")
                if p["type"] not in TYPES:
                    self.err(pw, f"unknown type {p['type']!r}")
                    continue
                if p["name"] in params:
                    self.err(pw, f"duplicate parameter {p['name']!r}")
                params[p["name"]] = TYPES[p["type"]]
            outcomes = []
            for j, g in enumerate(t["guards"]):
                gw = f"{w}.guards[{j}]"
                if not self.keys(gw, g, ("requirement", "when", "outcome")):
                    continue
                if g["requirement"] not in req_ids:
                    self.err(gw, f"unknown requirement {g['requirement']!r}")
                got = self.type_of(gw, g["when"], state, params)
                if got is not None and got != "bool":
                    self.err(gw, f"guard has type {got}, expected bool")
                outcomes.append(g["outcome"])
            o = t["otherwise"]
            ow = f"{w}.otherwise"
            if self.keys(ow, o, ("requirement", "outcome", "effect")):
                if o["requirement"] not in req_ids:
                    self.err(ow, f"unknown requirement {o['requirement']!r}")
                outcomes.append(o["outcome"])
                written = set()
                for j, a in enumerate(o["effect"]):
                    aw = f"{ow}.effect[{j}]"
                    if not self.keys(aw, a, ("var", "value")):
                        continue
                    if a["var"] not in state:
                        self.err(aw, f"assigns unknown state variable {a['var']!r}")
                        continue
                    if a["var"] in written:
                        self.err(aw, f"assigns {a['var']!r} twice")
                    written.add(a["var"])
                    got = self.type_of(aw, a["value"], state, params)
                    if got is not None and got != state[a["var"]]:
                        self.err(aw, f"value has type {got}, but {a['var']} is {state[a['var']]}")
            if len(set(outcomes)) != len(outcomes):
                self.err(w, "outcomes must be distinct")

        # invariants
        for i, inv in enumerate(ir["invariants"]):
            w = f"invariants[{i}]"
            if not self.keys(w, inv, ("id", "requirement", "statement", "body")):
                continue
            ids.append((w, inv["id"]))
            self.text(w, inv["statement"])
            if inv["requirement"] not in req_ids:
                self.err(w, f"unknown requirement {inv['requirement']!r}")
            got = self.type_of(w, inv["body"], state, {})
            if got is not None and got != "bool":
                self.err(w, f"invariant has type {got}, expected bool")

        # identifiers: well-formed and globally unique
        seen = {}
        for w, x in ids:
            if not isinstance(x, str) or not ID_RE.match(x):
                self.err(w, f"invalid identifier {x!r}")
            elif x in seen:
                self.err(w, f"duplicate identifier {x!r} (also {seen[x]})")
            else:
                seen[x] = w
        return self.errors


def check(ir, check_files=True):
    return Checker(ir, check_files).run()


# ---------------------------------------------------------------- interpreter
#
# A Python reading of `step` in formal/Step.lean, used to compute test-oracle
# expectations. It is NOT trusted: oracles generated with it are re-checked by
# the Lean kernel against the Lean specification.


class Stuck(IRError):
    pass


def eval_expr(e, state, params):
    (op, arg), = e.items()
    if op == "var":
        return state[arg]
    if op == "param":
        return params[arg]
    if op in ("bool", "nat"):
        return arg
    if op == "not":
        return not eval_expr(arg, state, params)
    if op == "nodup":
        xs = eval_expr(arg, state, params)
        return len(set(xs)) == len(xs)
    a, b = (eval_expr(x, state, params) for x in arg)
    if op == "and":
        return a and b
    if op == "or":
        return a or b
    if op == "eq_nat":
        return a == b
    if op == "contains":
        return b in a
    if op == "cons":
        return [a] + list(b)
    raise Stuck(f"unknown operator {op!r}")


def run_step(ir, transition_id, state, params):
    """Run one transition. Returns (new_state, outcome); `state` is not mutated."""
    matches = [t for t in ir["transitions"] if t["id"] == transition_id]
    if len(matches) != 1:
        raise IRError(f"no unique transition {transition_id!r}")
    tr = matches[0]
    for g in tr["guards"]:
        fired = eval_expr(g["when"], state, params)
        if not isinstance(fired, bool):
            raise Stuck(f"guard for {g['requirement']} is not Boolean")
        if fired:
            return dict(state), g["outcome"]
    # Simultaneous assignment: evaluate every right-hand side in the pre-state.
    writes = [(a["var"], eval_expr(a["value"], state, params)) for a in tr["otherwise"]["effect"]]
    new = dict(state)
    new.update(writes)
    return new, tr["otherwise"]["outcome"]


def holds(ir, invariant_id, state):
    matches = [i for i in ir["invariants"] if i["id"] == invariant_id]
    if len(matches) != 1:
        raise IRError(f"no unique invariant {invariant_id!r}")
    return eval_expr(matches[0]["body"], state, {}) is True


# ---------------------------------------------------------------- Lean generation


def lstr(s):
    return json.dumps(s, ensure_ascii=False)


def lexpr(e):
    (op, arg), = e.items()
    if op == "var":
        return f"(.var {lstr(arg)})"
    if op == "param":
        return f"(.param {lstr(arg)})"
    if op == "bool":
        return f"(.litBool {str(arg).lower()})"
    if op == "nat":
        return f"(.litNat {arg})"
    args = [arg] if len(OPS[op][0]) == 1 else arg
    return f"(.{LEAN_OP[op]} " + " ".join(lexpr(a) for a in args) + ")"


def llist(items, indent="    "):
    if not items:
        return "[]"
    return "[\n" + ",\n".join(indent + "  " + x for x in items) + "\n" + indent + "]"


def lanchors(prov):
    return "[" + ", ".join(
        f"⟨{lstr(a['artifact'])}, {lstr(a['anchor'])}, .{a['role']}⟩" for a in prov) + "]"


def lctx(vs):
    return "[" + ", ".join(f"({lstr(v['name'])}, .{TYPES[v['type']]})" for v in vs) + "]"


def generate_lean(ir, ident, source_rel):
    d = digest(ir)
    goals = [
        f"{{ id := {lstr(g['id'])}, parent := "
        + ("none" if g["parent"] is None else f"some {lstr(g['parent'])}")
        + f", provenance := {lanchors(g['provenance'])} }}"
        for g in ir["goals"]
    ]
    reqs = [
        f"{{ id := {lstr(r['id'])}, kind := .{r['kind']}, goals := "
        + "[" + ", ".join(lstr(x) for x in r["goals"]) + "]"
        + f", provenance := {lanchors(r['provenance'])} }}"
        for r in ir["requirements"]
    ]
    risks = [
        f"{{ id := {lstr(k['id'])}, status := .{k['status']}, mitigatedBy := "
        + "[" + ", ".join(lstr(x) for x in k["mitigated_by"]) + "]"
        + f", provenance := {lanchors(k['provenance'])} }}"
        for k in ir["risks"]
    ]
    trs = []
    for t in ir["transitions"]:
        guards = [f"{{ requirement := {lstr(g['requirement'])}, cond := {lexpr(g['when'])}, "
                  f"outcome := {lstr(g['outcome'])} }}" for g in t["guards"]]
        effect = [f"{{ var := {lstr(a['var'])}, value := {lexpr(a['value'])} }}"
                  for a in t["otherwise"]["effect"]]
        trs.append(
            "{ id := " + lstr(t["id"]) + ",\n"
            "        params := " + lctx(t["params"]) + ",\n"
            "        guards := " + llist(guards, "        ") + ",\n"
            "        otherwiseRequirement := " + lstr(t["otherwise"]["requirement"]) + ",\n"
            "        otherwiseOutcome := " + lstr(t["otherwise"]["outcome"]) + ",\n"
            "        effect := " + llist(effect, "        ") + " }")
    invs = [f"{{ id := {lstr(i['id'])}, requirement := {lstr(i['requirement'])}, "
            f"body := {lexpr(i['body'])} }}" for i in ir["invariants"]]
    arts = [f"{{ id := {lstr(a['id'])}, path := {lstr(a['path'])}, sha256 := {lstr(a['sha256'])} }}"
            for a in ir["artifacts"]]
    return "\n".join([
        "import ArtifactIR",
        "",
        f"/-! Auto-generated from {source_rel} (IR digest {d[:16]}).",
        f"DO NOT EDIT: python3 packages/ir/scripts/irc.py lean --write {source_rel} ...",
        "The theorem below is checked by the Lean kernel by evaluation (`decide`):",
        "it establishes that this IR instance satisfies `wellFormed`. -/",
        "",
        "open Architecton.IR",
        "",
        f"def {ident} : Model where",
        f"  goals := {llist(goals, '  ')}",
        f"  requirements := {llist(reqs, '  ')}",
        f"  risks := {llist(risks, '  ')}",
        f"  stateVars := {lctx(ir['state_vars'])}",
        f"  transitions := {llist(trs, '  ')}",
        f"  invariants := {llist(invs, '  ')}",
        f"  artifacts := {llist(arts, '  ')}",
        "",
        f"theorem {ident}_wellFormed : wellFormed {ident} = true := by decide",
        "",
        "/-- Consequence for this instance: every guard of every transition evaluates",
        "to a Boolean in every state and parameter environment that conforms to the",
        "declared types. -/",
        f"theorem {ident}_guards_evaluate {{tr : Transition}} (htr : tr ∈ {ident}.transitions)",
        "    {g : Guard} (hg : g ∈ tr.guards) {σ ρ : Env}",
        f"    (hσ : Conforms {ident}.stateVars σ) (hρ : Conforms tr.params ρ) :",
        "    ∃ b, eval σ ρ g.cond = some (.bool b) :=",
        f"  wf_guard_evaluates {ident}_wellFormed htr hg hσ hρ",
        "",
    ])


# ---------------------------------------------------------------- CLI


def rel(path):
    p = Path(path).resolve()
    try:
        return p.relative_to(REPO.resolve()).as_posix()
    except ValueError:
        return p.as_posix()


def cmd_check(args):
    failed = False
    for f in args.files:
        try:
            errors = check(load(f))
        except IRError as e:
            errors = [str(e)]
        if errors:
            failed = True
            print(f"FAIL {rel(f)}")
            for e in errors:
                print(f"  - {e}")
        else:
            print(f"PASS {rel(f)} (digest {digest(load(f))[:16]})")
    return 1 if failed else 0


def cmd_hash(args):
    path = Path(args.file)
    ir = load(path)
    changed = 0
    for a in ir.get("artifacts", []):
        new = artifact_hash(read_artifact(a["path"]))
        if a.get("sha256") != new:
            print(f"{a['id']}: {a['path']} -> {new[:12]}...")
            a["sha256"] = new
            changed += 1
    if not args.update:
        print(f"{changed} artifact hash(es) differ; rerun with --update after review")
        return 1 if changed else 0
    if changed:
        # Rewrite only the sha256 values to keep the hand-written layout.
        text = path.read_text(encoding="utf-8")
        for a in ir["artifacts"]:
            pattern = re.compile(r'("id":\s*' + re.escape(json.dumps(a["id"]))
                                 + r'[^{}]*?"sha256":\s*)"[0-9a-f]*"')
            text, n = pattern.subn(lambda m: m.group(1) + json.dumps(a["sha256"]), text)
            if n != 1:
                raise IRError(f"could not locate sha256 field for {a['id']}")
        path.write_text(text, encoding="utf-8", newline="\n")
    print(f"updated {changed} artifact hash(es)")
    return 0


def cmd_lean(args):
    ir = load(args.file)
    errors = check(ir)
    if errors:
        print("FAIL: IR does not check; fix it before generating Lean")
        for e in errors:
            print(f"  - {e}")
        return 1
    expected = generate_lean(ir, args.ident, rel(args.file))
    out = Path(args.out)
    if args.write:
        out.write_text(expected, encoding="utf-8", newline="\n")
        print(f"WROTE {rel(out)}")
        return 0
    actual = out.read_text(encoding="utf-8").replace("\r\n", "\n") if out.exists() else None
    if actual != expected:
        print(f"FAIL: {rel(out)} is out of date with {rel(args.file)}; run lean --write")
        return 1
    print(f"PASS {rel(out)} in sync with {rel(args.file)}")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check")
    c.add_argument("files", nargs="+")
    h = sub.add_parser("hash")
    h.add_argument("file")
    h.add_argument("--update", action="store_true")
    g = sub.add_parser("lean")
    g.add_argument("file")
    mode = g.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    g.add_argument("--out", required=True)
    g.add_argument("--ident", required=True)
    d = sub.add_parser("digest")
    d.add_argument("file")
    args = ap.parse_args(argv)
    try:
        if args.cmd == "check":
            return cmd_check(args)
        if args.cmd == "hash":
            return cmd_hash(args)
        if args.cmd == "lean":
            if not NAME_RE.match(args.ident):
                raise IRError(f"invalid Lean identifier {args.ident!r}")
            return cmd_lean(args)
        print(digest(load(args.file)))
        return 0
    except IRError as e:
        print(f"ERROR: {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
