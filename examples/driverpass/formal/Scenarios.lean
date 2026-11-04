/- Generated from contracts/scenarios.json. Checked by Lean `decide`. -/
import DriverPass

-- off-duty instructor is rejected
example : allocate { offDuty := true, slots := [10] } 11 =
  ({ offDuty := true, slots := [10] }, Decision.offDuty) := by decide

-- existing slot is rejected
example : allocate { offDuty := false, slots := [10, 9] } 10 =
  ({ offDuty := false, slots := [10, 9] }, Decision.duplicate) := by decide

-- free slot is assigned
example : allocate { offDuty := false, slots := [10, 9] } 11 =
  ({ offDuty := false, slots := [11, 10, 9] }, Decision.accepted) := by decide

-- empty roster is assigned
example : allocate { offDuty := false, slots := [] } 1 =
  ({ offDuty := false, slots := [1] }, Decision.accepted) := by decide

-- off-duty policy precedes duplication
example : allocate { offDuty := true, slots := [10] } 10 =
  ({ offDuty := true, slots := [10] }, Decision.offDuty) := by decide
