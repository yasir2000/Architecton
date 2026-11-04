// Auto-generated from requirements/policy.json (SHA-256 prefix b1590964089b173c).
// DO NOT EDIT: python3 scripts/generate.py
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Roster {
    pub off_duty: bool,
    pub slots: Vec<i64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Decision {
    Accepted,
    OffDuty,
    Duplicate,
}

// BR-001 -> BR-002 -> BR-003, with exactly the same guard priority as Lean.
pub fn allocate(s: &Roster, slot: i64) -> (Roster, Decision) {
    if s.off_duty {
        (s.clone(), Decision::OffDuty)
    } else if s.slots.contains(&slot) {
        (s.clone(), Decision::Duplicate)
    } else {
        let mut result = s.clone();
        result.slots.insert(0, slot);
        (result, Decision::Accepted)
    }
}
