#!/usr/bin/env python3
"""designc: well-formedness and conformance checks for design models.

Design diagrams are parsed as MODELS in a strict PlantUML subset (anything
outside the subset is an error, not silently ignored) and checked against the
formal model, the IR and the code:

  state    UML state machine  -> well-formed (one initial state, all states
           reachable, deterministic); generated Lean proves its semantics
           equal the lifecycle `step` (see `lean` below)
  sequence UML sequence       -> well-formed (declared participants, balanced
           alt/else/end); its transaction steps occur in the same order, under
           the same conditions, as in the code and the Lean model
  class    UML class          -> fields and enum literals agree with the IR,
           the Lean types and the Rust types
  archimate typed ArchiMate model (JSON) -> element and relationship types
           obey a conservative subset of the ArchiMate 3.2 relationship rules;
           every IR requirement is realized; every element traces to code

Commands (paths relative to the repository root):
  designc.py check SPEC.json...         run every check a conformance spec names
  designc.py lean --write|--check SPEC  generate the Lean diagram model (state)
This script is tested, not formally verified.
"""
import argparse
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]


class DesignError(Exception):
    pass


def read(rel):
    p = REPO / rel
    if not p.is_file():
        raise DesignError(f"file not found: {rel}")
    return p.read_text(encoding="utf-8").replace("\r\n", "\n")


def plantuml_lines(text, path):
    """Yield (lineno, line) of a PlantUML file, skipping comments, notes and
    presentation-only directives. Unknown directives are left for the caller."""
    lines = text.split("\n")
    in_note = False
    for n, raw in enumerate(lines, 1):
        line = raw.strip()
        if in_note:
            if line == "end note":
                in_note = False
            continue
        if not line or line.startswith("'"):
            continue
        if re.match(r"^note\b", line):
            if ":" not in line:  # multi-line note block
                in_note = True
            continue
        if line in ("@startuml", "@enduml") or re.match(r"^(title|hide|skinparam)\b", line):
            continue
        yield n, line
    if in_note:
        raise DesignError(f"{path}: unterminated note")


# ---------------------------------------------------------------- state machines

STATE_EDGE = re.compile(
    r"^(\[\*\]|[A-Za-z_]\w*)\s*-->\s*([A-Za-z_]\w*)"
    r"(?:\s*:\s*([A-Za-z_]\w*)(?:\s*\[([^\]]*)\])?(?:\s*/\s*(.*))?)?$")


def parse_state_machine(path):
    initial, edges = [], []
    for n, line in plantuml_lines(read(path), path):
        m = STATE_EDGE.match(line)
        if not m:
            raise DesignError(f"{path}:{n}: outside the state-machine subset: {line!r}")
        src, dst, event, guard, action = m.groups()
        if src == "[*]":
            if event:
                raise DesignError(f"{path}:{n}: the initial transition takes no event")
            initial.append(dst)
            continue
        if not event:
            raise DesignError(f"{path}:{n}: transition {src} --> {dst} has no event")
        conds = [g.strip() for g in guard.split("&&")] if guard and guard.strip() else []
        if any(not re.fullmatch(r"[A-Za-z_]\w*", c) for c in conds):
            raise DesignError(f"{path}:{n}: guard must be a conjunction of evidence names: [{guard}]")
        edges.append({"line": n, "src": src, "dst": dst, "event": event, "guard": conds,
                      "action": (action or "").strip()})
    return initial, edges


def check_state_machine(spec, errors):
    path = spec["diagram"]
    initial, edges = parse_state_machine(path)
    states = {e["src"] for e in edges} | {e["dst"] for e in edges} | set(initial)
    if len(initial) != 1:
        errors.append(f"{path}: needs exactly one initial transition, found {len(initial)}")
    # Reachability from the initial state.
    seen, todo = set(initial[:1]), list(initial[:1])
    while todo:
        s = todo.pop()
        for e in edges:
            if e["src"] == s and e["dst"] not in seen:
                seen.add(e["dst"])
                todo.append(e["dst"])
    for s in sorted(states - seen):
        errors.append(f"{path}: state {s} is unreachable")
    # Determinism: one transition per (state, event); guards here are evidence sets,
    # so two edges on the same state and event would overlap whenever both hold.
    by_key = {}
    for e in edges:
        key = (e["src"], e["event"])
        if key in by_key:
            errors.append(f"{path}:{e['line']}: nondeterministic: second '{e['event']}' "
                          f"from {e['src']} (first at line {by_key[key]['line']})")
        by_key.setdefault(key, e)
    # Vocabulary.
    state_map, events = spec["states"], set(spec["events"])
    for s in sorted(states):
        if s not in state_map:
            errors.append(f"{path}: state {s} has no counterpart in the formal model")
    for s in sorted(set(state_map) - states):
        errors.append(f"{path}: formal state {s} is missing from the diagram")
    evidence = set(spec["evidence"])
    for e in edges:
        if e["event"] not in events:
            errors.append(f"{path}:{e['line']}: unknown event {e['event']!r}")
        for g in e["guard"]:
            if g not in evidence:
                errors.append(f"{path}:{e['line']}: unknown evidence {g!r} in guard")
    # Conformance with the reviewed policy (the Lean `step` uses the generated gate).
    policy = json.loads(read(spec["policy"]))
    order = policy["phase_order"]
    inv = {v: k for k, v in state_map.items()}
    for i, phase in enumerate(order):
        name = inv.get(phase)
        promote = by_key.get((name, "promote"))
        nxt = order[i + 1] if i + 1 < len(order) else None
        if nxt is None:
            if promote:
                errors.append(f"{path}: {name} is terminal in the policy but has a promote edge")
            continue
        if not promote:
            errors.append(f"{path}: {name} lacks its promote edge")
            continue
        if state_map.get(promote["dst"]) != nxt:
            errors.append(f"{path}:{promote['line']}: promote from {name} goes to "
                          f"{promote['dst']}, policy says {nxt}")
        if sorted(promote["guard"]) != sorted(policy["required_evidence"][phase]):
            errors.append(f"{path}:{promote['line']}: promote guard {promote['guard']} != "
                          f"policy gate {policy['required_evidence'][phase]}")
    for name, phase in state_map.items():
        it = by_key.get((name, "iterate"))
        if not it or it["dst"] != name:
            errors.append(f"{path}: {name} needs an 'iterate' self-loop")
        rv = by_key.get((name, "reviseRequirements"))
        if not rv or state_map.get(rv["dst"]) != order[0]:
            errors.append(f"{path}: {name} needs 'reviseRequirements' back to {inv.get(order[0])}")
    if initial and state_map.get(initial[0]) != order[0]:
        errors.append(f"{path}: initial state {initial[0]} is not the policy's first phase")
    return initial, edges


def generate_state_lean(spec):
    initial, edges = parse_state_machine(spec["diagram"])
    sm = spec["states"]
    rows = ",\n".join(
        f"  {{ src := .{sm[e['src']]}, ev := .{e['event']}, "
        f"guard := [{', '.join('.' + g for g in e['guard'])}], dst := .{sm[e['dst']]} }}"
        for e in edges)
    return "\n".join([
        "import StateMachine",
        "",
        f"/-! Auto-generated by packages/design/scripts/designc.py from {spec['diagram']}.",
        "DO NOT EDIT. The diagram's transitions as data, its semantics as a function,",
        "and kernel-checked theorems that the diagram is deterministic, that every",
        "phase is reachable, and that it behaves exactly like the lifecycle `step`.",
        f"Abstracted (not drawn) events: {', '.join(spec['abstracted_events']) or 'none'}. -/",
        "",
        "namespace Architecton.Lifecycle.Diagram",
        "open Architecton.Lifecycle",
        "",
        "/-- The events the diagram draws. -/",
        "inductive Ev where",
        "  | " + " | ".join(spec["events"]),
        "  deriving DecidableEq, Repr",
        "",
        "def Ev.toCommand : Ev → Command",
        *[f"  | .{ev} => .{ev}" for ev in spec["events"]],
        "",
        "structure Edge where",
        "  src : Phase",
        "  ev : Ev",
        "  guard : List Evidence",
        "  dst : Phase",
        "  deriving DecidableEq, Repr",
        "",
        "def edges : List Edge := [",
        rows,
        "]",
        "",
        f"def initialPhase : Phase := .{sm[initial[0]]}",
        "",
        "/-- Diagram semantics: take the edge for (phase, event) if its guard holds;",
        "otherwise the event is blocked and the phase is unchanged. -/",
        "def diagramStep (s : ProcessState) (ev : Ev) : Phase × Outcome :=",
        "  match edges.find? (fun e => decide (e.src = s.phase) && decide (e.ev = ev)) with",
        "  | none => (s.phase, .blocked)",
        "  | some e => if e.guard.all s.verified.contains then (e.dst, .accepted) else (s.phase, .blocked)",
        "",
        "/-- At most one edge per (phase, event). -/",
        "theorem deterministic : ∀ p : Phase, ∀ ev : Ev,",
        "    (edges.filter (fun e => decide (e.src = p) && decide (e.ev = ev))).length ≤ 1 := by",
        "  intro p ev; cases p <;> cases ev <;> decide",
        "",
        "/-- The diagram starts where the model starts. -/",
        "theorem initial_agrees : initialPhase = initial.phase := by decide",
        "",
        "/-- **Conformance.** For every process state and every drawn event, the",
        "diagram reaches the same phase with the same outcome as the lifecycle `step`. -/",
        "theorem diagram_matches_step (s : ProcessState) (ev : Ev) :",
        "    diagramStep s ev = ((step s ev.toCommand).1.phase, (step s ev.toCommand).2) := by",
        "  obtain ⟨phase, iteration, revision, verified, archive⟩ := s",
        "  cases ev <;> cases phase <;>",
        "    simp [diagramStep, edges, step, Ev.toCommand, nextPhase, gateSatisfied, List.find?] <;>",
        "    (repeat' split) <;> simp_all",
        "",
        "end Architecton.Lifecycle.Diagram",
        "",
    ])


# ---------------------------------------------------------------- sequence diagrams

PARTICIPANT = re.compile(r'^(actor|participant|database)\s+(?:"([^"]+)"\s+as\s+)?([A-Za-z_]\w*)$')
MESSAGE = re.compile(r"^([A-Za-z_]\w*)\s*(-->|->)\s*([A-Za-z_]\w*)\s*:\s*(.+)$")


def parse_sequence(path):
    participants, messages, stack = {}, [], []
    for n, line in plantuml_lines(read(path), path):
        if m := PARTICIPANT.match(line):
            participants[m.group(3)] = m.group(2) or m.group(3)
            continue
        if m := MESSAGE.match(line):
            a, arrow, b, label = m.groups()
            for p in (a, b):
                if p not in participants:
                    raise DesignError(f"{path}:{n}: undeclared participant {p!r}")
            messages.append({"line": n, "from": a, "to": b, "reply": arrow == "-->",
                             "label": label.strip(), "conditions": [c for c, _ in stack]})
            continue
        if m := re.match(r"^alt\s+(.+)$", line):
            stack.append((m.group(1).strip(), n))
            continue
        if m := re.match(r"^else\s+(.+)$", line):
            if not stack:
                raise DesignError(f"{path}:{n}: else outside alt")
            stack[-1] = (m.group(1).strip(), stack[-1][1])
            continue
        if line == "end":
            if not stack:
                raise DesignError(f"{path}:{n}: end without alt")
            stack.pop()
            continue
        raise DesignError(f"{path}:{n}: outside the sequence subset: {line!r}")
    if stack:
        raise DesignError(f"{path}:{stack[-1][1]}: alt never closed")
    return participants, messages


def ordered_positions(text, anchors, where, errors):
    """Positions of each anchor in `text`, in order; report missing or out-of-order."""
    pos, last = [], -1
    for a in anchors:
        i = text.find(a, last + 1)
        if i < 0:
            errors.append(f"{where}: {a!r} not found after the previous step"
                          + (" (exists earlier: order differs)" if a in text else ""))
            return pos
        pos.append(i)
        last = i
    return pos


def check_sequence(spec, errors):
    path = spec["diagram"]
    _, messages = parse_sequence(path)
    steps = spec["steps"]
    # 1. The diagram shows the steps in order, each under its declared condition.
    idx = -1
    for st in steps:
        found = [k for k, m in enumerate(messages) if k > idx and m["label"] == st["diagram"]]
        if not found:
            errors.append(f"{path}: step {st['name']!r} ({st['diagram']!r}) missing or out of order")
            continue
        idx = found[0]
        m = messages[idx]
        if m["conditions"] != st.get("when", []):
            errors.append(f"{path}:{m['line']}: step {st['name']!r} drawn under {m['conditions']}, "
                          f"expected {st.get('when', [])}")
    # 2. The code performs them in the same order.
    code = read(spec["code"]["file"])
    start = code.find(spec["code"]["function"])
    if start < 0:
        errors.append(f"{spec['code']['file']}: {spec['code']['function']!r} not found")
    else:
        ordered_positions(code[start:], [st["code"] for st in steps],
                          f"{spec['code']['file']}::{spec['code']['function']}", errors)
    # 3. The Lean model performs them in the same order (textual check of the
    #    model's definition; its behaviour is proved separately).
    lean = read(spec["lean"]["file"])
    start = lean.find(spec["lean"]["definition"])
    if start < 0:
        errors.append(f"{spec['lean']['file']}: {spec['lean']['definition']!r} not found")
    else:
        body = lean[start:lean.find("\n\n", start)]
        ordered_positions(body, [st["lean"] for st in steps if st.get("lean")],
                          f"{spec['lean']['file']}::{spec['lean']['definition']}", errors)


# ---------------------------------------------------------------- class diagrams

CLASS_OPEN = re.compile(r"^(class|enum)\s+([A-Za-z_]\w*)(?:\s+<<\w+>>)?\s*\{$")
FIELD = re.compile(r"^[+\-#~]?\s*([A-Za-z_]\w*)\s*(?::\s*(.+))?$")
ASSOC = re.compile(r"^([A-Za-z_]\w*)\s*(-->|--|\.\.>|<\|--|\*--|o--)\s*([A-Za-z_]\w*)(?:\s*:\s*.+)?$")


def parse_classes(path):
    classes, current, assocs = {}, None, []
    for n, line in plantuml_lines(read(path), path):
        if current is not None:
            if line == "}":
                current = None
                continue
            m = FIELD.match(line)
            if not m or "(" in line:
                if "(" in line:  # operation: recorded, not type-checked
                    classes[current]["operations"].append(line.lstrip("+-#~ "))
                    continue
                raise DesignError(f"{path}:{n}: outside the class subset: {line!r}")
            classes[current]["members"][m.group(1)] = (m.group(2) or "").strip()
            continue
        if m := CLASS_OPEN.match(line):
            current = m.group(2)
            classes[current] = {"kind": m.group(1), "members": {}, "operations": []}
            continue
        if m := ASSOC.match(line):
            assocs.append((m.group(1), m.group(3), n))
            continue
        raise DesignError(f"{path}:{n}: outside the class subset: {line!r}")
    for a, b, n in assocs:
        for c in (a, b):
            if c not in classes:
                raise DesignError(f"{path}:{n}: association to undeclared class {c!r}")
    return classes


def check_classes(spec, errors):
    path = spec["diagram"]
    classes = parse_classes(path)
    ir = json.loads(read(spec["ir"]))
    state = {v["name"]: v["type"] for v in ir["state_vars"]}
    for cls, binding in spec["state_class"].items():
        if cls not in classes:
            errors.append(f"{path}: class {cls} missing")
            continue
        members = classes[cls]["members"]
        for field, ir_var in binding["fields"].items():
            if field not in members:
                errors.append(f"{path}: {cls}.{field} missing")
            elif ir_var not in state:
                errors.append(f"{path}: {cls}.{field} maps to unknown IR state {ir_var!r}")
            elif spec["types"].get(members[field]) != state[ir_var]:
                errors.append(f"{path}: {cls}.{field} : {members[field]} does not match "
                              f"IR {ir_var} : {state[ir_var]}")
        extra = set(members) - set(binding["fields"]) - set(binding.get("keys", []))
        for f in sorted(extra):
            errors.append(f"{path}: {cls}.{f} has no IR counterpart (declare it as a key or map it)")
    for enum, binding in spec["outcome_enum"].items():
        if enum not in classes or classes[enum]["kind"] != "enum":
            errors.append(f"{path}: enum {enum} missing")
            continue
        literals = set(classes[enum]["members"])
        outcomes = {g["outcome"] for t in ir["transitions"] for g in t["guards"]}
        outcomes |= {t["otherwise"]["outcome"] for t in ir["transitions"]}
        if literals != outcomes:
            errors.append(f"{path}: {enum} literals {sorted(literals)} != IR outcomes {sorted(outcomes)}")
        lean = read(binding["lean_file"])
        m = re.search(r"inductive\s+" + re.escape(enum) + r"\s+where(.*?)deriving", lean, re.S)
        lean_ctors = set(re.findall(r"\|\s*(\w+)", m.group(1))) if m else set()
        want = {re.sub(r"_(\w)", lambda x: x.group(1).upper(), lit) for lit in literals}
        if lean_ctors != want:
            errors.append(f"{binding['lean_file']}: {enum} constructors {sorted(lean_ctors)} != "
                          f"diagram {sorted(want)} (camelCase)")
        rust = read(binding["rust_file"])
        m = re.search(r"pub enum\s+" + re.escape(enum) + r"\s*\{(.*?)\}", rust, re.S)
        variants = re.findall(r"(\w+)\s*,", m.group(1)) if m else []
        snake = {re.sub(r"(?<!^)([A-Z])", r"_\1", v).lower() for v in variants}
        if 'rename_all = "snake_case"' not in rust or snake != literals:
            errors.append(f"{binding['rust_file']}: {enum} serializes as {sorted(snake)}, "
                          f"diagram says {sorted(literals)}")


# ---------------------------------------------------------------- ArchiMate

LAYERS = {
    "Goal": "motivation", "Requirement": "motivation", "Constraint": "motivation",
    "BusinessProcess": "business", "BusinessActor": "business",
    "ApplicationComponent": "application", "ApplicationService": "application",
    "ApplicationFunction": "application", "ApplicationInterface": "application",
    "DataObject": "application",
    "Node": "technology", "SystemSoftware": "technology", "Artifact": "technology",
}
CORE = {t for t, layer in LAYERS.items() if layer != "motivation"}
BEHAVIOR = {"BusinessProcess", "ApplicationService", "ApplicationFunction"}

# A conservative SUBSET of the ArchiMate 3.2 relationship rules: only pairings
# this model needs, each allowed by the specification. Anything else is rejected,
# even if the full specification (Appendix B) would allow it.
ALLOWED = {
    "realization": {
        ("Requirement", "Goal"), ("Constraint", "Goal"),
        ("ApplicationComponent", "ApplicationService"), ("ApplicationFunction", "ApplicationService"),
        ("Artifact", "ApplicationComponent"), ("Artifact", "DataObject"),
        *{(c, "Requirement") for c in CORE}, *{(c, "Constraint") for c in CORE},
    },
    "assignment": {("ApplicationComponent", "ApplicationFunction"), ("Node", "Artifact"),
                   ("SystemSoftware", "Artifact"), ("BusinessActor", "BusinessProcess")},
    "serving": {("ApplicationService", "BusinessProcess"), ("SystemSoftware", "ApplicationComponent"),
                ("Node", "ApplicationComponent"), ("ApplicationInterface", "BusinessActor"),
                ("ApplicationService", "BusinessActor")},
    "access": {("ApplicationFunction", "DataObject"), ("ApplicationService", "DataObject")},
    "composition": {("Node", "SystemSoftware"), ("ApplicationComponent", "ApplicationInterface")},
    "triggering": {("ApplicationFunction", "ApplicationFunction"), ("BusinessProcess", "BusinessProcess")},
}


def check_archimate(spec, errors):
    path = spec["model"]
    model = json.loads(read(path))
    elements = {}
    for e in model["elements"]:
        if e["id"] in elements:
            errors.append(f"{path}: duplicate element {e['id']}")
        if e["type"] not in LAYERS:
            errors.append(f"{path}: {e['id']}: unknown or unsupported type {e['type']!r}")
        elements[e["id"]] = e
        for t in e.get("trace", []):
            text = read(t["file"]) if (REPO / t["file"]).is_file() else None
            if text is None:
                errors.append(f"{path}: {e['id']}: trace file {t['file']} not found")
            elif t["anchor"] not in text:
                errors.append(f"{path}: {e['id']}: anchor {t['anchor']!r} not in {t['file']}")
        if LAYERS.get(e["type"]) != "motivation" and not e.get("trace"):
            errors.append(f"{path}: {e['id']}: core element without a trace to an artifact")
    for r in model["relationships"]:
        a, b, kind = elements.get(r["from"]), elements.get(r["to"]), r["type"]
        if a is None or b is None:
            errors.append(f"{path}: relationship {r} names an unknown element")
            continue
        if kind not in ALLOWED:
            errors.append(f"{path}: unknown relationship type {kind!r}")
        elif (a["type"], b["type"]) not in ALLOWED[kind]:
            errors.append(f"{path}: {kind} {a['type']} {a['id']} -> {b['type']} {b['id']} "
                          "is not in the supported ArchiMate subset")
    # Trace completeness against the IR.
    ir = json.loads(read(spec["ir"]))
    realized = {r["to"] for r in model["relationships"] if r["type"] == "realization"}
    for req in ir["requirements"]:
        if req["id"] not in elements:
            errors.append(f"{path}: IR requirement {req['id']} has no ArchiMate element")
        elif req["id"] not in realized:
            errors.append(f"{path}: requirement {req['id']} is realized by no element")
    for g in ir["goals"]:
        if g["parent"] is None and g["id"] not in elements:
            errors.append(f"{path}: IR root goal {g['id']} has no ArchiMate element")


# ---------------------------------------------------------------- CLI

CHECKS = {"state": check_state_machine, "sequence": check_sequence,
          "class": check_classes, "archimate": check_archimate}


def run_spec(spec_path):
    spec = json.loads(Path(spec_path).read_text(encoding="utf-8"))
    errors = []
    for item in spec["checks"]:
        kind = item["kind"]
        if kind not in CHECKS:
            errors.append(f"unknown check kind {kind!r}")
            continue
        try:
            CHECKS[kind](item, errors)
        except DesignError as e:
            errors.append(str(e))
    return spec, errors


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check")
    c.add_argument("specs", nargs="+")
    g = sub.add_parser("lean")
    mode = g.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    g.add_argument("spec")
    args = ap.parse_args(argv)
    if args.cmd == "check":
        failed = False
        for s in args.specs:
            spec, errors = run_spec(s)
            kinds = ", ".join(i["kind"] for i in spec["checks"])
            if errors:
                failed = True
                print(f"FAIL {s} ({kinds})")
                for e in errors:
                    print(f"  - {e}")
            else:
                print(f"PASS {s} ({kinds})")
        return 1 if failed else 0
    spec = json.loads(Path(args.spec).read_text(encoding="utf-8"))
    states = [i for i in spec["checks"] if i["kind"] == "state"]
    if len(states) != 1:
        print("ERROR: the spec must contain exactly one state check")
        return 2
    st = states[0]
    errors = []
    try:
        check_state_machine(st, errors)
    except DesignError as e:
        errors.append(str(e))
    if errors:
        print("FAIL: fix the diagram before generating Lean:\n  - " + "\n  - ".join(errors))
        return 1
    out = REPO / st["lean_out"]
    text = generate_state_lean(st)
    if args.write:
        out.write_text(text, encoding="utf-8", newline="\n")
        print(f"WROTE {st['lean_out']}")
        return 0
    if not out.is_file() or out.read_text(encoding="utf-8").replace("\r\n", "\n") != text:
        print(f"FAIL: {st['lean_out']} is out of date; run lean --write")
        return 1
    print(f"PASS {st['lean_out']} in sync with {st['diagram']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
