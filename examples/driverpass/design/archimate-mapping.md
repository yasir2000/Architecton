# ArchiMate-inspired architecture-to-implementation mapping

This is a documented mapping, **not** a certified ArchiMate interchange file.

> **Superseded as the source of truth** by the typed model [architecture.json](architecture.json), which `packages/design/scripts/designc.py` checks against a subset of the ArchiMate 3.2 relationship rules, the IR requirements and the code. This table remains as a readable summary.

| Architecture layer | Modeling element | POC realization | Trace |
|---|---|---|---|
| Motivation | Business requirement | BR-001–BR-003 in `requirements/policy.json` | Guards / final effect |
| Motivation | Constraint | SR-001 no mutation on rejection | `rejected_preserves_roster` |
| Business | Business process | Assign instructor slot | `design/sequence.puml` |
| Application | Application service | Allocation API | `backend/src/main.rs` |
| Application | Application function | Decision function | `formal/DriverPass.lean`, `backend/src/domain.rs` |
| Application | Data object | InstructorRoster, Decision | `design/domain.puml` |
| Technology | System software | Rust/Axum, SQLite | `backend/Cargo.toml` |
| Technology | Node / deployment | Docker container with persistent SQLite volume | `infra/` |

A production ArchiMate model would additionally contain authentic elements, relationships,
viewpoints, and import/export via a modeling tool. This table avoids pretending that a UML
class is itself an ArchiMate entity or that a diagram proves correctness.
