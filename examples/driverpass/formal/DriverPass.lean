/- Auto-generated from requirements/policy.json (SHA-256 prefix b1590964089b173c).
   DO NOT EDIT: python3 scripts/generate.py -/

inductive Decision where
  | accepted
  | offDuty
  | duplicate
  deriving Repr, DecidableEq

structure Roster where
  offDuty : Bool
  slots : List Nat
  deriving Repr, DecidableEq

/-- The policy's ordered decision table. A pure transition relation. -/
def allocate (s : Roster) (slot : Nat) : Roster × Decision :=
  if s.offDuty then
    (s, Decision.offDuty)
  else if s.slots.contains slot then
    (s, Decision.duplicate)
  else
    ({ s with slots := slot :: s.slots }, Decision.accepted)
