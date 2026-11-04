# DriverPass source integration and verification status

Architecton includes two original requirement/design documents and two wider Lean formalizations:

| Artifact | Current role | Formal execution coverage |
|---|---|---|
| [Business Requirements Document](../CS%20255%20Business%20Requirements%20Document%20Template.docx) | Stakeholder requirements and quality constraints | Analyst interpretation required |
| [System Design Document](../CS%20255%20System%20Design%20Document%20Template.docx) | UML use-case/activity/sequence/class views | Diagram semantics not automatically proved |
| [DriverPass.lean](../DriverPass.lean) | Formalized users/roles, offline access, authentication, scheduling | Independent of narrower example CI |
| [DriverPassDesign.lean](../DriverPassDesign.lean) | Formalized design operations and stated design gaps | Independent of narrower example CI |
| [Instructor-slot example](../examples/driverpass/) | End-to-end transition policy, model, implementation, HTTP and SQLite | Dedicated CI workflow |

## Boundaries

The BRD includes package purchases, appointments, user authorization, offline read/online edit, failed-login lockout, DMV notification, and performance requirements. The system design includes UML views for login and paid appointment scheduling. The example's `requirements/policy.json` captures **only a selected instructor-slot rule**; not every phrase in the original documents entails the PoC's additional duplicate-assignment and audit-policy decisions. These are explicit modeling choices.

There is no automatic parser proving that a Word BRD or a pictorial UML diagram entails the Lean definitions. The translation is a human-reviewed traceability step.

## Next formal engineering milestone

Define a typed requirements IR with requirement IDs, source anchors, guarded transitions, refinement conditions, and proof obligations. Then provide machine-checked simulation relations between that IR, Lean executable semantics, and separately implemented Rust transitions.

The original broader Lean source formalizations should be integrated into an additional verification job once their import boundaries and toolchain compatibility have been confirmed.
