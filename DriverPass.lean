/-
DriverPass — formalization of the CS 255 Business Requirements Document.

Each section cites the BRD bullet it formalizes. Requirements that are about
real-world performance or platforms (load time < 2 s, browser support,
monthly updates, responsive UI) cannot be proved about a model and are
listed as out of scope at the bottom of this file.

Plain Lean 4 core, no Mathlib needed.
-/

namespace DriverPass

/-! ## 1. Users, roles, connectivity
BRD: "manage multiple user roles and permissions", "access data offline,
edit data online", "Customer users ... access to their own account",
"Admin users ... access to the entire schedule ... spoof customer accounts". -/

inductive Role
  | customer
  | employee
  | admin
  deriving DecidableEq, Repr

structure User where
  id   : Nat
  role : Role
  deriving DecidableEq, Repr

inductive Connectivity
  | online
  | offline
  deriving DecidableEq, Repr

inductive Action
  | read (owner : Nat)        -- read data of account `owner`
  | edit (owner : Nat)        -- change data of account `owner`
  | viewFullSchedule
  | bookFor (customer : Nat)  -- make a reservation for `customer`
  deriving DecidableEq, Repr

/-- Customers may only touch their own account; staff may touch any. -/
def canAccessAccount (u : User) (owner : Nat) : Bool :=
  match u.role with
  | .customer => owner == u.id
  | _         => true

def permitted (u : User) : Connectivity → Action → Bool
  | _,        .read owner       => canAccessAccount u owner
  | .online,  .edit owner       => canAccessAccount u owner
  | .offline, .edit _           => false
  | _,        .viewFullSchedule =>
      match u.role with
      | .customer => false
      | _         => true
  | .online,  .bookFor cust     => canAccessAccount u cust
  | .offline, .bookFor _        => false

/-- BRD: "allow employees to access the data offline". -/
theorem offline_read_allowed (u : User) (o : Nat) (h : canAccessAccount u o = true) :
    permitted u .offline (.read o) = true := by
  simp [permitted, h]

/-- BRD: "Edits to the data should be made online only." -/
theorem offline_edit_denied (u : User) (o : Nat) :
    permitted u .offline (.edit o) = false := by
  simp [permitted]

theorem offline_booking_denied (u : User) (o : Nat) :
    permitted u .offline (.bookFor o) = false := by
  simp [permitted]

/-- BRD: customers get access to *their own* account only. -/
theorem customer_cannot_read_others (u : User) (c : Connectivity) (o : Nat)
    (h : u.role = .customer) (hne : o ≠ u.id) :
    permitted u c (.read o) = false := by
  cases c <;> simp [permitted, canAccessAccount, h, hne]

theorem customer_cannot_edit_others (u : User) (c : Connectivity) (o : Nat)
    (h : u.role = .customer) (hne : o ≠ u.id) :
    permitted u c (.edit o) = false := by
  cases c <;> simp [permitted, canAccessAccount, h, hne]

theorem customer_cannot_book_for_others (u : User) (c : Connectivity) (o : Nat)
    (h : u.role = .customer) (hne : o ≠ u.id) :
    permitted u c (.bookFor o) = false := by
  cases c <;> simp [permitted, canAccessAccount, h, hne]

theorem customer_cannot_view_full_schedule (u : User) (c : Connectivity)
    (h : u.role = .customer) :
    permitted u c .viewFullSchedule = false := by
  cases c <;> simp [permitted, h]

/-- BRD: admins can "spoof customer user accounts to make appointments on
their behalf". -/
theorem admin_can_book_for_anyone (u : User) (cust : Nat) (h : u.role = .admin) :
    permitted u .online (.bookFor cust) = true := by
  simp [permitted, canAccessAccount, h]

/-! ## 2. Login, 2FA, lockout, password reset
BRD Security + Functional Requirements:
* "The system shall validate user password when logging in."
* "Passwords are case-sensitive."
* "send a verification SMS ... when 2FA is enabled."
* "lock user accounts after five consecutive failed logins."
* "send email with temporary password in the event of account lock or
  forgotten password." -/

inductive Message
  | tempPassword
  | smsCode
  | dmvRuleChange
  deriving DecidableEq, Repr

def maxAttempts : Nat := 5

structure Account where
  password       : String
  twoFactor      : Bool := false
  failedAttempts : Nat := 0
  locked         : Bool := false
  outbox         : List Message := []   -- emails / SMS sent to this user

inductive LoginResult
  | success
  | wrongPassword
  | lockedOut
  deriving DecidableEq, Repr

/-- Messages after a successful password check: an SMS code iff 2FA is on. -/
def outboxAfterSuccess (a : Account) : List Message :=
  if a.twoFactor then .smsCode :: a.outbox else a.outbox

def login (a : Account) (attempt : String) : LoginResult × Account :=
  if a.locked then
    (.lockedOut, a)
  else if attempt = a.password then
    (.success, { a with failedAttempts := 0, outbox := outboxAfterSuccess a })
  else if maxAttempts ≤ a.failedAttempts + 1 then
    (.lockedOut, { a with failedAttempts := a.failedAttempts + 1, locked := true,
                          outbox := .tempPassword :: a.outbox })
  else
    (.wrongPassword, { a with failedAttempts := a.failedAttempts + 1 })

/-- Run a sequence of login attempts. -/
def loginAll : Account → List String → Account
  | a, []      => a
  | a, p :: ps => loginAll (login a p).2 ps

/-- Login succeeds only on an unlocked account with the *exact* password.
`=` on `String` is exact, so this is also the case-sensitivity requirement:
"Secret" never authenticates an account whose password is "secret". -/
theorem login_success_only_with_exact_password (a : Account) (p : String)
    (h : (login a p).1 = .success) : a.locked = false ∧ p = a.password := by
  unfold login at h
  split at h
  next => simp at h
  next hl =>
    split at h
    next hp => exact ⟨by simpa using hl, hp⟩
    next => split at h <;> simp at h

theorem correct_password_logs_in (a : Account) (hl : a.locked = false) :
    (login a a.password).1 = .success := by
  simp [login, hl]

/-- 2FA: a successful login on a 2FA account sends an SMS code. -/
theorem two_factor_sends_sms (a : Account) (hl : a.locked = false)
    (h2 : a.twoFactor = true) :
    .smsCode ∈ (login a a.password).2.outbox := by
  simp [login, outboxAfterSuccess, hl, h2]

/-- A locked account rejects every attempt, even the correct password. -/
theorem locked_rejects (a : Account) (p : String) (h : a.locked = true) :
    (login a p).1 = .lockedOut := by
  simp [login, h]

theorem locked_persist : ∀ (ps : List String) (a : Account),
    a.locked = true → (loginAll a ps).locked = true
  | [],      _, h => h
  | p :: ps, a, h => by
    simp only [loginAll]
    apply locked_persist ps
    simp [login, h]

/-- The failure that reaches the limit locks the account *and* emails a
temporary password. -/
theorem lockout_sends_temp_password (a : Account) (p : String)
    (hl : a.locked = false) (hp : p ≠ a.password)
    (hn : maxAttempts ≤ a.failedAttempts + 1) :
    (login a p).1 = .lockedOut ∧ (login a p).2.locked = true ∧
      .tempPassword ∈ (login a p).2.outbox := by
  simp [login, hl, hp, hn]

/-- "Lock user accounts after five consecutive failed logins": starting from
any unlocked account, enough consecutive wrong passwords lock it. -/
theorem consecutive_failures_lock : ∀ (ps : List String) (a : Account),
    a.locked = false → (∀ p ∈ ps, p ≠ a.password) →
    maxAttempts ≤ a.failedAttempts + ps.length → ps ≠ [] →
    (loginAll a ps).locked = true
  | [],      _, _,  _,  _,    hne => absurd rfl hne
  | p :: ps, a, hl, hw, hlen, _   => by
    have hp : p ≠ a.password := hw p (by simp)
    simp only [loginAll]
    by_cases hn : maxAttempts ≤ a.failedAttempts + 1
    · apply locked_persist
      simp [login, hl, hp, hn]
    · have hstep : (login a p).2 = { a with failedAttempts := a.failedAttempts + 1 } := by
        simp [login, hl, hp, hn]
      rw [hstep]
      apply consecutive_failures_lock ps
      · exact hl
      · intro q hq
        exact hw q (by simp [hq])
      · show maxAttempts ≤ a.failedAttempts + 1 + ps.length
        simp only [List.length_cons] at hlen
        omega
      · intro h
        subst h
        simp only [List.length_cons, List.length_nil] at hlen
        omega

/-- Corollary with the BRD's number: 5 wrong passwords on a fresh account. -/
theorem five_failures_lock (a : Account) (ps : List String)
    (hl : a.locked = false) (h0 : a.failedAttempts = 0)
    (hlen : ps.length = 5) (hw : ∀ p ∈ ps, p ≠ a.password) :
    (loginAll a ps).locked = true := by
  apply consecutive_failures_lock ps a hl hw
  · simp [maxAttempts, h0, hlen]
  · intro h
    subst h
    simp at hlen

/-- Forgotten password: emails a temporary password. -/
def forgotPassword (a : Account) : Account :=
  { a with outbox := .tempPassword :: a.outbox }

theorem forgot_password_sends_temp (a : Account) :
    .tempPassword ∈ (forgotPassword a).outbox := by
  simp [forgotPassword]

/-! ## 3. Scheduling
BRD: "track available appointment times and user appointments",
"schedule user appointments in response to user or admin commands". -/

structure Booking where
  customer : Nat
  driver   : Nat
  slot     : Nat
  deriving DecidableEq, Repr

structure Schedule where
  available : List (Nat × Nat)   -- open (driver, slot) pairs
  bookings  : List Booking

def book (s : Schedule) (b : Booking) : Option Schedule :=
  if (b.driver, b.slot) ∈ s.available then
    some { available := s.available.filter (· != (b.driver, b.slot)),
           bookings  := b :: s.bookings }
  else
    none

/-- Who may book: checks the permission rules from section 1 first. -/
def requestBooking (u : User) (c : Connectivity) (s : Schedule) (b : Booking) :
    Option Schedule :=
  if permitted u c (.bookFor b.customer) then book s b else none

theorem booking_needs_open_slot (s s' : Schedule) (b : Booking)
    (h : book s b = some s') : (b.driver, b.slot) ∈ s.available := by
  unfold book at h
  split at h
  next hm => exact hm
  next => simp at h

theorem booking_recorded (s s' : Schedule) (b : Booking)
    (h : book s b = some s') : b ∈ s'.bookings := by
  unfold book at h
  split at h
  next =>
    cases h
    simp
  next => simp at h

/-- No double booking: once a driver's slot is taken, it cannot be booked
again (by anyone). -/
theorem no_double_booking (s s' : Schedule) (b b' : Booking)
    (h : book s b = some s') (hd : b'.driver = b.driver) (hs : b'.slot = b.slot) :
    book s' b' = none := by
  unfold book at h
  split at h
  next =>
    cases h
    simp [book, hd, hs, List.mem_filter]
  next => simp at h

theorem customer_booking_for_other_rejected (u : User) (c : Connectivity)
    (s : Schedule) (b : Booking) (h : u.role = .customer) (hne : b.customer ≠ u.id) :
    requestBooking u c s b = none := by
  simp [requestBooking, customer_cannot_book_for_others u c b.customer h hne]

/-! ## 4. Audit trail
BRD: "track changes made by each employee", "Edits ... online only". -/

structure EditRecord where
  editor : Nat
  owner  : Nat
  field  : String
  deriving DecidableEq, Repr

structure Db where
  data : List (Nat × String × String)   -- (owner, field, value)
  log  : List EditRecord

def applyEdit (u : User) (c : Connectivity) (owner : Nat) (field value : String)
    (db : Db) : Option Db :=
  if permitted u c (.edit owner) then
    some { data := (owner, field, value) :: db.data,
           log  := ⟨u.id, owner, field⟩ :: db.log }
  else
    none

/-- Every accepted edit is logged with the editor's id. -/
theorem edit_is_logged (u : User) (c : Connectivity) (o : Nat) (f v : String)
    (db db' : Db) (h : applyEdit u c o f v db = some db') :
    (⟨u.id, o, f⟩ : EditRecord) ∈ db'.log := by
  unfold applyEdit at h
  split at h
  next =>
    cases h
    simp
  next => simp at h

/-- The log is append-only: an edit never removes earlier entries. -/
theorem log_append_only (u : User) (c : Connectivity) (o : Nat) (f v : String)
    (db db' : Db) (h : applyEdit u c o f v db = some db') :
    ∀ e ∈ db.log, e ∈ db'.log := by
  unfold applyEdit at h
  split at h
  next =>
    cases h
    intro e he
    simp [he]
  next => simp at h

theorem offline_edit_rejected (u : User) (o : Nat) (f v : String) (db : Db) :
    applyEdit u .offline o f v db = none := by
  simp [applyEdit, offline_edit_denied]

/-! ## 5. DMV rule-change notification
BRD: "The system shall notify admins when DMV rules change." -/

def notifyDmvChange (users : List User) : List (Nat × Message) :=
  (users.filter (fun u => u.role == .admin)).map (fun u => (u.id, .dmvRuleChange))

theorem every_admin_notified (users : List User) (u : User)
    (hu : u ∈ users) (h : u.role = .admin) :
    (u.id, Message.dmvRuleChange) ∈ notifyDmvChange users := by
  unfold notifyDmvChange
  exact List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu, by simp [h]⟩, rfl⟩

/-! ## Out of scope (not provable about a model)
* Load time ≤ 2 s; ≤ 2 h downtime per monthly update (operational SLAs)
* Browser / mobile compatibility, responsive UI
* Session cookies, IT admin server access, daily error reports
* Package types (BRD gives no package contents to formalize)
-/

end DriverPass
