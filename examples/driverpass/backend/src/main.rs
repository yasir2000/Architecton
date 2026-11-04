//! Minimal executable infrastructure adapter for a Lean-specified decision rule.
//! Educational PoC: localhost-only deployment; no authentication; single-process SQLite.
use axum::{
    extract::{Path, State},
    http::StatusCode,
    routing::{get, patch, post},
    Json, Router,
};
use driverpass_poc::domain::{allocate, Decision, Roster};
use rusqlite::{params, Connection, OptionalExtension, TransactionBehavior};
use serde::Deserialize;
use serde_json::{json, Value};
use std::{env, net::SocketAddr, sync::{Arc, Mutex}};

#[derive(Clone)]
struct AppState {
    db: Arc<Mutex<Connection>>,
}

type ApiResponse = (StatusCode, Json<Value>);

fn reply(status: StatusCode, body: Value) -> ApiResponse {
    (status, Json(body))
}

fn db_error(error: impl std::fmt::Display) -> ApiResponse {
    eprintln!("database error: {error}");
    reply(StatusCode::INTERNAL_SERVER_ERROR, json!({"error":"database_error"}))
}

fn load_roster(db: &Connection, instructor_id: i64) -> rusqlite::Result<Option<Roster>> {
    let duty: Option<i64> = db
        .query_row(
            "SELECT off_duty FROM instructors WHERE id = ?1",
            [instructor_id],
            |row| row.get(0),
        )
        .optional()?;
    let Some(duty) = duty else { return Ok(None) };
    let mut stmt = db.prepare(
        "SELECT slot_id FROM allocations WHERE instructor_id = ?1 ORDER BY seq DESC",
    )?;
    let slots = stmt
        .query_map([instructor_id], |row| row.get::<_, i64>(0))?
        .collect::<rusqlite::Result<Vec<_>>>()?;
    Ok(Some(Roster { off_duty: duty != 0, slots }))
}

#[derive(Deserialize)]
struct SlotRequest {
    slot_id: i64,
}

#[derive(Deserialize)]
struct DutyRequest {
    off_duty: bool,
}

async fn health() -> ApiResponse {
    reply(StatusCode::OK, json!({"status":"ok"}))
}

async fn get_instructor(State(state): State<AppState>, Path(id): Path<i64>) -> ApiResponse {
    let db = state.db.lock().expect("SQLite mutex poisoned");
    match load_roster(&db, id) {
        Ok(Some(roster)) => reply(StatusCode::OK, json!({"id":id,"roster":roster})),
        Ok(None) => reply(StatusCode::NOT_FOUND, json!({"error":"unknown_instructor"})),
        Err(e) => db_error(e),
    }
}

async fn update_duty(
    State(state): State<AppState>,
    Path(id): Path<i64>,
    Json(request): Json<DutyRequest>,
) -> ApiResponse {
    let mut db = state.db.lock().expect("SQLite mutex poisoned");
    let tx = match db.transaction_with_behavior(TransactionBehavior::Immediate) {
        Ok(tx) => tx,
        Err(e) => return db_error(e),
    };
    let changed = match tx.execute(
        "UPDATE instructors SET off_duty = ?1 WHERE id = ?2",
        params![i64::from(request.off_duty), id],
    ) {
        Ok(changed) => changed,
        Err(e) => return db_error(e),
    };
    if changed == 0 {
        return reply(StatusCode::NOT_FOUND, json!({"error":"unknown_instructor"}));
    }
    let roster = match load_roster(&tx, id) {
        Ok(Some(roster)) => roster,
        Ok(None) => return db_error("updated instructor disappeared"),
        Err(e) => return db_error(e),
    };
    if let Err(e) = tx.commit() { return db_error(e) }
    reply(StatusCode::OK, json!({"id":id,"roster":roster}))
}

async fn assign_slot(
    State(state): State<AppState>,
    Path(id): Path<i64>,
    Json(request): Json<SlotRequest>,
) -> ApiResponse {
    // Lean uses Nat; the HTTP/SQL boundary accepts only nonnegative i64.
    if request.slot_id < 0 {
        return reply(StatusCode::BAD_REQUEST, json!({"error":"slot_id_must_be_nonnegative"}));
    }
    let mut db = state.db.lock().expect("SQLite mutex poisoned");
    // Serializes read/decide/write, preventing concurrent double bookings in this SQLite PoC.
    let tx = match db.transaction_with_behavior(TransactionBehavior::Immediate) {
        Ok(tx) => tx,
        Err(e) => return db_error(e),
    };
    let current = match load_roster(&tx, id) {
        Ok(Some(roster)) => roster,
        Ok(None) => return reply(StatusCode::NOT_FOUND, json!({"error":"unknown_instructor"})),
        Err(e) => return db_error(e),
    };
    let (expected, decision) = allocate(&current, request.slot_id);
    if decision == Decision::Accepted {
        if let Err(e) = tx.execute(
            "INSERT INTO allocations(instructor_id, slot_id) VALUES (?1, ?2)",
            params![id, request.slot_id],
        ) { return db_error(e) }
    }
    if let Err(e) = tx.execute(
        "INSERT INTO allocation_audit(instructor_id, slot_id, decision) VALUES (?1, ?2, ?3)",
        params![id, request.slot_id, decision_name(decision)],
    ) { return db_error(e) }
    if let Err(e) = tx.commit() { return db_error(e) }
    reply(
        if decision == Decision::Accepted { StatusCode::CREATED } else { StatusCode::CONFLICT },
        json!({"id":id,"decision":decision,"roster":expected}),
    )
}

fn decision_name(decision: Decision) -> &'static str {
    match decision {
        Decision::Accepted => "accepted",
        Decision::OffDuty => "off_duty",
        Decision::Duplicate => "duplicate",
    }
}

async fn audit(State(state): State<AppState>) -> ApiResponse {
    let db = state.db.lock().expect("SQLite mutex poisoned");
    let mut stmt = match db.prepare(
        "SELECT instructor_id, slot_id, decision FROM allocation_audit ORDER BY id DESC LIMIT 50",
    ) {
        Ok(s) => s,
        Err(e) => return db_error(e),
    };
    let entries = stmt.query_map([], |row| {
        Ok(json!({
            "instructor_id": row.get::<_, i64>(0)?,
            "slot_id": row.get::<_, i64>(1)?,
            "decision": row.get::<_, String>(2)?
        }))
    });
    match entries.and_then(|iter| iter.collect::<rusqlite::Result<Vec<_>>>()) {
        Ok(rows) => reply(StatusCode::OK, json!({"entries":rows})),
        Err(e) => db_error(e),
    }
}

fn initialize(conn: &Connection) -> rusqlite::Result<()> {
    conn.execute_batch(
        "PRAGMA foreign_keys=ON;
         PRAGMA journal_mode=WAL;
         PRAGMA synchronous=FULL;
         PRAGMA busy_timeout=5000;
         CREATE TABLE IF NOT EXISTS instructors (
            id INTEGER PRIMARY KEY CHECK(id >= 0),
            off_duty INTEGER NOT NULL CHECK(off_duty IN (0,1))
         );
         CREATE TABLE IF NOT EXISTS allocations (
            seq INTEGER PRIMARY KEY AUTOINCREMENT,
            instructor_id INTEGER NOT NULL REFERENCES instructors(id),
            slot_id INTEGER NOT NULL CHECK(slot_id >= 0),
            UNIQUE(instructor_id, slot_id)
         );
         CREATE TABLE IF NOT EXISTS allocation_audit (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            instructor_id INTEGER NOT NULL REFERENCES instructors(id),
            slot_id INTEGER NOT NULL CHECK(slot_id >= 0),
            decision TEXT NOT NULL CHECK(decision IN ('accepted','off_duty','duplicate')),
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
         );
         INSERT OR IGNORE INTO instructors(id, off_duty) VALUES (7, 0);"
    )
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = env::var("DATABASE_PATH").unwrap_or_else(|_| "driverpass.db".to_owned());
    let port: u16 = env::var("PORT").unwrap_or_else(|_| "3000".into()).parse()?;
    let host = env::var("HOST").unwrap_or_else(|_| "127.0.0.1".into());
    let db = Connection::open(path)?;
    initialize(&db)?;
    let state = AppState { db: Arc::new(Mutex::new(db)) };
    let app = Router::new()
        .route("/health", get(health))
        .route("/api/v1/instructors/{id}", get(get_instructor))
        .route("/api/v1/instructors/{id}/duty", patch(update_duty))
        .route("/api/v1/instructors/{id}/slots", post(assign_slot))
        .route("/api/v1/audit", get(audit))
        .with_state(state);
    let addr: SocketAddr = format!("{host}:{port}").parse()?;
    let listener = tokio::net::TcpListener::bind(addr).await?;
    println!("DriverPass verification PoC listening at http://{addr}");
    axum::serve(listener, app).await?;
    Ok(())
}
