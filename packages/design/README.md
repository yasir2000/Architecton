# Design refinements

Treats the design diagrams as **models that are checked**, not pictures. [scripts/designc.py](scripts/designc.py) parses a strict PlantUML subset: anything outside the subset is an error, never silently skipped. It then checks each diagram against the formal model, the typed IR and the code.

| Model | Well-formedness | Conformance |
|---|---|---|
| UML state machine: [phase-state-machine.puml](../lifecycle/design/phase-state-machine.puml) | one initial state; every state reachable; one transition per (state, event); known events and evidence | promote edges follow the policy's phase order and gates; every phase has `iterate` and `reviseRequirements`. **Lean proof** that the diagram behaves exactly like the lifecycle `step` |
| UML sequence: [sequence.puml](../../examples/driverpass/design/sequence.puml) | declared participants; balanced `alt`/`else`/`end` | transaction steps appear in the same order, under the same conditions, in the diagram, in `service.rs` and in the Lean model `assignTx` |
| UML class: [domain.puml](../../examples/driverpass/design/domain.puml) | declared classes; known members | `InstructorRoster` fields match the IR state's names and types; `Decision` literals equal the IR outcomes, the Lean constructors and the Rust serde names |
| ArchiMate: [architecture.json](../../examples/driverpass/design/architecture.json) | element and relationship types obey a conservative subset of the ArchiMate 3.2 rules | every IR requirement is an element realized by some element; every core element traces to a file anchor that exists |

The specs that bind diagrams to models are [packages/lifecycle/design/conformance.json](../lifecycle/design/conformance.json) and [examples/driverpass/design/conformance.json](../../examples/driverpass/design/conformance.json).

## The state-diagram proof

`designc.py lean` turns the state diagram into data, [PhaseDiagram.lean](../lifecycle/formal/PhaseDiagram.lean), with a semantics function `diagramStep`. The Lean kernel proves:

- `diagram_matches_step`: for **every** process state and every drawn event, the diagram reaches the same phase with the same outcome as the lifecycle model's `step`;
- `deterministic`: at most one edge per phase and event (no axioms);
- `initial_agrees`: the diagram starts where the model starts.

`recordValidated` is a declared abstraction: the model has it, but the diagram doesn't draw it. The proof covers phase and outcome only, not iteration counters or the evidence archive.

## Tests

[tests/test_designc.py](tests/test_designc.py) has 30 tests. Most break one thing in memory: a weakened gate, a skipped phase, swapped transaction steps in the diagram, the code or the Lean model, a renamed enum literal, a disallowed ArchiMate relationship, a broken trace. Each must produce its specific error. Separately, generating Lean from a diagram with a weakened gate makes the Lean proof fail, so the conformance proof doesn't depend on trusting the Python checker.

## Run checks

```bash
python3 -m unittest discover -s packages/design/tests -v
python3 packages/design/scripts/designc.py check \
    packages/lifecycle/design/conformance.json examples/driverpass/design/conformance.json
python3 packages/design/scripts/designc.py lean --check packages/lifecycle/design/conformance.json
cd packages/lifecycle && LEAN_PATH=formal lean formal/PhaseDiagram.lean   # after building StateMachine
```

After a reviewed change to the state diagram, regenerate the Lean with `lean --write`.

## Limits

- **Activity diagrams aren't covered yet.** The repository has none, and I didn't invent one.
- **Sequence and code order is checked textually.** The checker finds each step's anchor in order within the function body. That catches reordering, but not, for example, a step moved into a loop. The Lean model's *behaviour* is proved separately in `Transactions.lean`.
- **ArchiMate coverage is a subset.** Only the relationship pairings this model needs are allowed, each one permitted by the ArchiMate 3.2 specification; anything else is rejected even if the full rule table (Appendix B) would allow it. There is no Open Group exchange-format import or export.
- **PlantUML subset.** Styling, notes and titles are ignored, as they don't change meaning. Every other construct outside the subset makes the check fail.
