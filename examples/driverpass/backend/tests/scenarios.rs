use driverpass_poc::domain::{allocate, Decision, Roster};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct Scenario {
    name: String,
    before: Roster,
    slot_id: i64,
    expected: Expected,
}

#[derive(Debug, Deserialize)]
struct Expected {
    decision: Decision,
    roster: Roster,
}

#[test]
fn shared_semantic_scenarios_match() {
    let scenarios: Vec<Scenario> =
        serde_json::from_str(include_str!("../../contracts/scenarios.json"))
            .expect("valid shared contract scenarios");
    assert!(scenarios.len() >= 5);
    for case in scenarios {
        let (roster, decision) = allocate(&case.before, case.slot_id);
        assert_eq!(decision, case.expected.decision, "{}", case.name);
        assert_eq!(roster, case.expected.roster, "{}", case.name);
    }
}

#[test]
fn bounded_invariant_sweep() {
    for off_duty in [true, false] {
        for held in 0..=15 {
            for requested in 0..=15 {
                let before = Roster {
                    off_duty,
                    slots: vec![held],
                };
                let (after, decision) = allocate(&before, requested);
                if decision != Decision::Accepted {
                    assert_eq!(after, before);
                } else {
                    assert!(!off_duty);
                    assert_ne!(held, requested);
                    assert_eq!(after.slots, vec![requested, held]);
                }
            }
        }
    }
}
