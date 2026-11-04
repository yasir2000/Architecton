/-
DriverPass — formalization of the CS 255 System Design Document.

Sources (UML diagrams in the design document):
* Class diagram       → section 1 (data model)
* Login activity      → section 2 (login state machine)
* Schedule activity   → section 3 (scheduling with payment)
* Sequence diagram    → section 3 (confirmation only after payment verified)
* Use case diagram    → sections 2–5 (failed-login tracking, forgot password,
                        instructor time off, DMV notification)

Each theorem is a property the design guarantees. Comments marked GAP are
places where the design is ambiguous or disagrees with the BRD
(see DriverPass.lean).

Plain Lean 4 core, no Mathlib needed.
-/

namespace DriverPassDesign

/-! ## 1. Class diagram -/

/-- `AppointmentSlot(startTime, endTime : DateTime)`; times in minutes. -/
structure AppointmentSlot where
  startTime : Nat
  endTime   : Nat
  deriving DecidableEq, Repr

/-- GAP: the class diagram does not require `startTime < endTime`. -/
def AppointmentSlot.WellFormed (s : AppointmentSlot) : Prop :=
  s.startTime < s.endTime

/-- `User(email, password, phone, twoFactor)`. -/
structure User where
  id        : Nat
  email     : String
  password  : String
  phone     : Nat
  twoFactor : Bool

/-- Subclasses of `User`. GAP: the BRD has office employees who book for
customers; the class diagram has no such class. -/
inductive Actor
  | customer (id : Nat)
  | instructor (id : Nat)
  | administrator (id : Nat)
  deriving DecidableEq, Repr

/-- `Appointment(instructor, customer, slot)`. -/
structure Appointment where
  instructor : Nat
  customer   : Nat
  slot       : AppointmentSlot
  deriving DecidableEq, Repr

/-- `Customer.scheduleAppointment(slot)` books for the customer themself;
`Administrator.scheduleAppointment(customer, slot)` books for anyone;
`Instructor` has no `scheduleAppointment`. -/
def mayScheduleFor : Actor → Nat → Bool
  | .customer id,      c => id == c
  | .administrator _,  _ => true
  | .instructor _,     _ => false

theorem customer_schedules_only_for_self (id c : Nat)
    (h : mayScheduleFor (.customer id) c = true) : c = id := by
  simp [mayScheduleFor] at h
  omega

theorem administrator_schedules_for_anyone (id c : Nat) :
    mayScheduleFor (.administrator id) c = true := rfl

theorem instructor_cannot_schedule (id c : Nat) :
    mayScheduleFor (.instructor id) c = false := rfl

/-! ## 2. Login activity diagram
Prompt for password → incorrect: add 1 to consecutive failed attempts;
fewer than five → prompt again; five → "Reset password, lock account".
Correct → 2FA enabled? send SMS, prompt for code; correct code → log in,
incorrect code → "Reset password, lock account". 2FA off → log in. -/

def maxAttempts : Nat := 5

inductive LoginState
  | awaitingPassword (failures : Nat)
  | awaitingSms
  | loggedIn
  | locked
  deriving DecidableEq, Repr

inductive Input
  | password (p : String)
  | smsCode (c : Nat)
  deriving DecidableEq, Repr

inductive Msg
  | sms
  | tempPassword
  deriving DecidableEq, Repr

/-- The account being logged into; `smsCode` is the code that was sent. -/
structure Account where
  password  : String
  twoFactor : Bool
  smsCode   : Nat

structure Session where
  state  : LoginState
  outbox : List Msg

def Session.start : Session := ⟨.awaitingPassword 0, []⟩

/-- "Reset password, lock account". -/
def lockAndReset (s : Session) : Session :=
  ⟨.locked, .tempPassword :: s.outbox⟩

def afterCorrectPassword (acct : Account) (s : Session) : Session :=
  if acct.twoFactor then ⟨.awaitingSms, .sms :: s.outbox⟩ else ⟨.loggedIn, s.outbox⟩

def step (acct : Account) (s : Session) (i : Input) : Session :=
  match s.state, i with
  | .awaitingPassword n, .password p =>
      if p = acct.password then afterCorrectPassword acct s
      else if n + 1 < maxAttempts then ⟨.awaitingPassword (n + 1), s.outbox⟩
      else lockAndReset s
  | .awaitingSms, .smsCode c =>
      if c = acct.smsCode then ⟨.loggedIn, s.outbox⟩ else lockAndReset s
  | _, _ => s   -- other inputs are ignored; `loggedIn` and `locked` are final

def run (acct : Account) : Session → List Input → Session
  | s, []      => s
  | s, i :: is => run acct (step acct s i) is

theorem correct_password_no_2fa_logs_in (acct : Account) (n : Nat) (o : List Msg)
    (h : acct.twoFactor = false) :
    (step acct ⟨.awaitingPassword n, o⟩ (.password acct.password)).state = .loggedIn := by
  simp [step, afterCorrectPassword, h]

/-- With 2FA on, a correct password alone does *not* log in: it sends an SMS
and waits for the code. -/
theorem correct_password_2fa_sends_sms (acct : Account) (n : Nat) (o : List Msg)
    (h : acct.twoFactor = true) :
    step acct ⟨.awaitingPassword n, o⟩ (.password acct.password) =
      ⟨.awaitingSms, .sms :: o⟩ := by
  simp [step, afterCorrectPassword, h]

theorem correct_sms_logs_in (acct : Account) (o : List Msg) :
    (step acct ⟨.awaitingSms, o⟩ (.smsCode acct.smsCode)).state = .loggedIn := by
  simp [step]

/-- GAP: one wrong SMS code locks the account immediately. The BRD only asks
for a lock after five failed logins. -/
theorem wrong_sms_locks (acct : Account) (o : List Msg) (c : Nat)
    (h : c ≠ acct.smsCode) :
    step acct ⟨.awaitingSms, o⟩ (.smsCode c) = ⟨.locked, .tempPassword :: o⟩ := by
  simp [step, lockAndReset, h]

theorem wrong_password_counts (acct : Account) (n : Nat) (o : List Msg) (p : String)
    (hp : p ≠ acct.password) (hn : n + 1 < maxAttempts) :
    step acct ⟨.awaitingPassword n, o⟩ (.password p) = ⟨.awaitingPassword (n + 1), o⟩ := by
  simp [step, hp, hn]

theorem limit_reached_locks_and_resets (acct : Account) (n : Nat) (o : List Msg)
    (p : String) (hp : p ≠ acct.password) (hn : ¬ n + 1 < maxAttempts) :
    step acct ⟨.awaitingPassword n, o⟩ (.password p) = ⟨.locked, .tempPassword :: o⟩ := by
  simp [step, lockAndReset, hp, hn]

theorem locked_is_final (acct : Account) (o : List Msg) (i : Input) :
    step acct ⟨.locked, o⟩ i = ⟨.locked, o⟩ := by
  cases i <;> rfl

theorem logged_in_is_final (acct : Account) (o : List Msg) (i : Input) :
    step acct ⟨.loggedIn, o⟩ i = ⟨.loggedIn, o⟩ := by
  cases i <;> rfl

theorem run_locked (acct : Account) : ∀ (is : List Input) (o : List Msg),
    run acct ⟨.locked, o⟩ is = ⟨.locked, o⟩
  | [],      _ => rfl
  | i :: is, o => by
    simp only [run, locked_is_final]
    exact run_locked acct is o

/-- Enough consecutive wrong passwords always end in a locked account. -/
theorem consecutive_failures_lock (acct : Account) : ∀ (ps : List String) (n : Nat)
    (o : List Msg), (∀ p ∈ ps, p ≠ acct.password) →
    maxAttempts ≤ n + ps.length → ps ≠ [] →
    (run acct ⟨.awaitingPassword n, o⟩ (ps.map Input.password)).state = .locked
  | [],      _, _, _,  _,    hne => absurd rfl hne
  | p :: ps, n, o, hw, hlen, _   => by
    have hp : p ≠ acct.password := hw p (by simp)
    simp only [List.map_cons, run]
    by_cases hn : n + 1 < maxAttempts
    · rw [wrong_password_counts acct n o p hp hn]
      apply consecutive_failures_lock acct ps (n + 1) o
      · intro q hq
        exact hw q (by simp [hq])
      · simp only [List.length_cons] at hlen
        omega
      · intro h
        subst h
        simp only [List.length_cons, List.length_nil] at hlen
        omega
    · rw [limit_reached_locks_and_resets acct n o p hp hn, run_locked]

/-- The diagram's number: five wrong passwords from a fresh login lock it. -/
theorem five_wrong_passwords_lock (acct : Account) (ps : List String)
    (hlen : ps.length = 5) (hw : ∀ p ∈ ps, p ≠ acct.password) :
    (run acct Session.start (ps.map Input.password)).state = .locked := by
  apply consecutive_failures_lock acct ps 0 [] hw
  · simp [maxAttempts, hlen]
  · intro h
    subst h
    simp at hlen

/-- Use case "Forgot password" → "Reset password". -/
def forgotPassword (s : Session) : Session :=
  ⟨s.state, .tempPassword :: s.outbox⟩

theorem forgot_password_sends_temp (s : Session) :
    .tempPassword ∈ (forgotPassword s).outbox := by
  simp [forgotPassword]

/-! ## 3. Schedule activity + sequence diagram
Display available slots → select → payment method (saved or new) → verify
payment. Failure → notify user, ask for payment method again. Success →
remove slot from available slots → confirm to customer → notify instructor.
The payment processor is external, so its answer is an input. -/

inductive PaymentMethod
  | saved (id : Nat)     -- `Customer.paymentMethods : Array<int>`
  | new (info : String)
  deriving DecidableEq, Repr

inductive PaymentResult
  | verified
  | failed
  deriving DecidableEq, Repr

inductive Notice
  | confirmation (a : Appointment)       -- to the customer
  | instructorNotice (a : Appointment)   -- to the instructor
  | paymentFailed (customer : Nat)
  | dmvRuleChange (admin : Nat)
  deriving DecidableEq, Repr

inductive Outcome
  | confirmed
  | paymentFailed
  | slotUnavailable
  deriving DecidableEq, Repr

structure State where
  /-- `Instructor.availableSlots`, flattened to (instructor, slot) pairs. -/
  openSlots    : List (Nat × AppointmentSlot)
  appointments : List Appointment
  outbox       : List Notice

/-- `AppointmentSlot.getAvailableInstructors`. -/
def getAvailableInstructors (st : State) (slot : AppointmentSlot) : List Nat :=
  (st.openSlots.filter (fun x => decide (x.2 = slot))).map Prod.fst

theorem mem_getAvailableInstructors (st : State) (i : Nat) (slot : AppointmentSlot) :
    i ∈ getAvailableInstructors st slot ↔ (i, slot) ∈ st.openSlots := by
  unfold getAvailableInstructors
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨j, s⟩, hx, rfl⟩
    rw [List.mem_filter] at hx
    have hs : s = slot := by simpa using hx.2
    subst hs
    exact hx.1
  · intro h
    exact ⟨(i, slot), List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩

/-- Success path: remove slot, confirm to customer, notify instructor. -/
def confirm (st : State) (a : Appointment) : State :=
  { openSlots    := st.openSlots.filter (fun x => decide (x ≠ (a.instructor, a.slot)))
    appointments := a :: st.appointments
    outbox       := .instructorNotice a :: .confirmation a :: st.outbox }

/-- Failure path: notify user; nothing else changes. -/
def failPayment (st : State) (a : Appointment) : State :=
  { st with outbox := .paymentFailed a.customer :: st.outbox }

def scheduleAppointment (st : State) (a : Appointment) (payment : PaymentResult) :
    Outcome × State :=
  if (a.instructor, a.slot) ∈ st.openSlots then
    match payment with
    | .verified => (.confirmed, confirm st a)
    | .failed   => (.paymentFailed, failPayment st a)
  else
    (.slotUnavailable, st)

/-- Sequence diagram: "Appointment confirmed" only after "Payment verified",
and only for a slot that was available. -/
theorem confirmed_only_if_paid (st : State) (a : Appointment) (p : PaymentResult)
    (h : (scheduleAppointment st a p).1 = .confirmed) :
    p = .verified ∧ (a.instructor, a.slot) ∈ st.openSlots := by
  by_cases hm : (a.instructor, a.slot) ∈ st.openSlots
  · cases p
    · exact ⟨rfl, hm⟩
    · simp [scheduleAppointment, hm] at h
  · simp [scheduleAppointment, hm] at h

/-- Success: the slot leaves the available list, the appointment is stored,
and both the customer and the instructor are notified. -/
theorem payment_success_effects (st : State) (a : Appointment)
    (hm : (a.instructor, a.slot) ∈ st.openSlots) :
    let st' := (scheduleAppointment st a .verified).2
    (a.instructor, a.slot) ∉ st'.openSlots ∧ a ∈ st'.appointments ∧
      .confirmation a ∈ st'.outbox ∧ .instructorNotice a ∈ st'.outbox := by
  simp [scheduleAppointment, confirm, hm, List.mem_filter]

/-- Failure: no slot is taken, no appointment is created, the user is told. -/
theorem payment_failure_effects (st : State) (a : Appointment)
    (hm : (a.instructor, a.slot) ∈ st.openSlots) :
    let st' := (scheduleAppointment st a .failed).2
    st'.openSlots = st.openSlots ∧ st'.appointments = st.appointments ∧
      .paymentFailed a.customer ∈ st'.outbox := by
  simp [scheduleAppointment, failPayment, hm]

/-- No double booking: once confirmed, the same instructor and slot cannot be
booked again, whatever the payment result. -/
theorem no_double_booking (st : State) (a b : Appointment) (p q : PaymentResult)
    (h : (scheduleAppointment st a p).1 = .confirmed)
    (hi : b.instructor = a.instructor) (hs : b.slot = a.slot) :
    (scheduleAppointment (scheduleAppointment st a p).2 b q).1 = .slotUnavailable := by
  obtain ⟨rfl, hm⟩ := confirmed_only_if_paid st a p h
  simp [scheduleAppointment, confirm, hm, hi, hs, List.mem_filter]

/-! ## 4. Instructor.requestTimeOff -/

def requestTimeOff (st : State) (instr : Nat) (off : List AppointmentSlot) : State :=
  { st with openSlots := st.openSlots.filter (fun x => decide (¬ (x.1 = instr ∧ x.2 ∈ off))) }

theorem time_off_removes_slot (st : State) (instr : Nat) (off : List AppointmentSlot)
    (s : AppointmentSlot) (h : s ∈ off) :
    (instr, s) ∉ (requestTimeOff st instr off).openSlots := by
  simp [requestTimeOff, List.mem_filter, h]

/-- GAP: time off does not touch appointments that are already booked in
those slots. The design does not say whether they are cancelled. -/
theorem time_off_keeps_appointments (st : State) (instr : Nat)
    (off : List AppointmentSlot) :
    (requestTimeOff st instr off).appointments = st.appointments := rfl

/-! ## 5. Use case "Notify admins when DMV rules change" -/

def notifyDmvChange (admins : List Nat) (st : State) : State :=
  { st with outbox := admins.map Notice.dmvRuleChange ++ st.outbox }

theorem every_admin_notified (admins : List Nat) (st : State) (adm : Nat)
    (h : adm ∈ admins) :
    .dmvRuleChange adm ∈ (notifyDmvChange admins st).outbox := by
  simp [notifyDmvChange, h]

/-! ## Out of scope
* Host machine, internet connection, office computer with browser
  (Technical Requirements) — deployment, not behavior
* `Customer.processPayment(method : int, amount : float)` — GAP: money as
  `float` invites rounding errors; this model treats the processor's answer
  as an input and never computes amounts
* BRD requirements with no counterpart in the design: offline read access,
  online-only edits, per-employee edit tracking, package types
-/

end DriverPassDesign
