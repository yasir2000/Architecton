# ArchiMate-inspired architecture-to-implementation mapping

This is a documented mapping, **not** a certified ArchiMate interchange file.

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
