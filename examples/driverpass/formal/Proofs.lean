import DriverPass

/-! Human-authored proof obligations, checked against the GENERATED specification.
    These proofs contain no `sorry` and introduce no project-specific axioms. -/

-- BR-001: The roster is unchanged when the instructor is off duty.
theorem offDuty_denied (s : Roster) (slot : Nat)
    (h : s.offDuty = true) :
    allocate s slot = (s, Decision.offDuty) := by
  simp [allocate, h]

-- BR-002: An on-duty instructor cannot receive an already-assigned slot.
theorem duplicate_denied (s : Roster) (slot : Nat)
    (hd : s.offDuty = false)
    (hc : s.slots.contains slot = true) :
    allocate s slot = (s, Decision.duplicate) := by
  have hm : slot ∈ s.slots := by simpa using hc
  simp [allocate, hd, hm]

-- SR-001: Every non-successful transition preserves the entire roster.
theorem rejected_preserves_roster (s : Roster) (slot : Nat)
    (h : (allocate s slot).2 ≠ Decision.accepted) :
    (allocate s slot).1 = s := by
  cases hd : s.offDuty with
  | true => simp [allocate, hd]
  | false =>
      cases hc : s.slots.contains slot with
      | true =>
          have hm : slot ∈ s.slots := by simpa using hc
          simp [allocate, hd, hm]
      | false =>
          have hm : slot ∉ s.slots := by simpa using hc
          simp [allocate, hd, hm] at h

-- BR-003: A successful transition prepends exactly the requested slot.
theorem accepted_prepends_slot (s : Roster) (slot : Nat)
    (h : (allocate s slot).2 = Decision.accepted) :
    (allocate s slot).1.slots = slot :: s.slots := by
  cases hd : s.offDuty with
  | true => simp [allocate, hd] at h
  | false =>
      cases hc : s.slots.contains slot with
      | true =>
          have hm : slot ∈ s.slots := by simpa using hc
          simp [allocate, hd, hm] at h
      | false =>
          have hm : slot ∉ s.slots := by simpa using hc
          simp [allocate, hd, hm]
