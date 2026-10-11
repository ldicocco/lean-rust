/-!
# Chapter 25 · Typestate in Lean

Protocol states as indices of a family of types: a connection
`Conn : ConnState → Type` whose operations exist only in the right state, the
observation that Lean (which is not affine) lets you reuse an old state, and
a vault indexed by a *runtime value*, its balance, so that overdrawing is a
type error or a proof obligation.
-/

namespace Ch25.Typestate

/-! ## A connection -/

-- ANCHOR: conn
/-- The states of the protocol, as an ordinary inductive type. -/
inductive ConnState where
  | closed | connected | authenticated
  deriving Repr, DecidableEq

/-- A connection in state `s`. The state appears only in the type: no field
mentions it, and Lean, unlike Rust, does not mind. -/
structure Conn (s : ConnState) where
  host : String
  sent : List String    -- what has gone over the wire, for the demo
  deriving Repr
-- ANCHOR_END: conn

-- ANCHOR: conn_family
/-- info: Conn : ConnState → Type -/
#guard_msgs in
#check @Conn
-- ANCHOR_END: conn_family

-- ANCHOR: conn_ops
def Conn.new (host : String) : Conn .closed := ⟨host, []⟩

def Conn.connect (c : Conn .closed) : Conn .connected :=
  ⟨c.host, c.sent ++ ["HELLO"]⟩

def Conn.login (c : Conn .connected) (user : String) : Conn .authenticated :=
  ⟨c.host, c.sent ++ [s!"LOGIN {user}"]⟩

def Conn.query (c : Conn .authenticated) (sql : String) : Conn .authenticated :=
  ⟨c.host, c.sent ++ [s!"QUERY {sql}"]⟩

/-- Available in every state: `s` is an implicit argument. -/
def Conn.close {s : ConnState} (c : Conn s) : Conn .closed :=
  ⟨c.host, c.sent ++ ["BYE"]⟩
-- ANCHOR_END: conn_ops

-- ANCHOR: conn_session
/-- info: { host := "db", sent := ["HELLO", "LOGIN lab", "QUERY SELECT 1", "BYE"] } -/
#guard_msgs in
#eval ((Conn.new "db").connect.login "lab" |>.query "SELECT 1").close
-- ANCHOR_END: conn_session

-- ANCHOR: wrong_state
/--
error: Application type mismatch: The argument
  (Conn.new "db").connect
has type
  Conn ConnState.connected
but is expected to have type
  Conn ConnState.authenticated
in the application
  (Conn.new "db").connect.query
-/
#guard_msgs in
def tooEarly := (Conn.new "db").connect.query "SELECT 1"
-- ANCHOR_END: wrong_state

-- ANCHOR: reuse
/-- Lean is not affine: the old state `c` can be used twice. For an
immutable value this is harmless; it would not be for a live socket. -/
def connectTwice (c : Conn .closed) : Conn .connected × Conn .connected :=
  (c.connect, c.connect)
-- ANCHOR_END: reuse

/-! ## A vault indexed by its balance -/

-- ANCHOR: vault
/-- A vault whose type records its balance. The balance is not a field: it
is the index, and `Vault.balance` reads it back from the type. -/
structure Vault (balance : Nat) where
  owner : String

def Vault.open (owner : String) : Vault 0 := ⟨owner⟩

def Vault.deposit {b : Nat} (v : Vault b) (amount : Nat) : Vault (b + amount) :=
  ⟨v.owner⟩

/-- Withdrawing requires a proof that the balance suffices. The body does not
use the proof (hence the underscore); the type checker does. -/
def Vault.withdraw {b : Nat} (v : Vault b) (amount : Nat)
    (_enough : amount ≤ b) : Vault (b - amount) :=
  ⟨v.owner⟩

def Vault.balance {b : Nat} (_ : Vault b) : Nat := b
-- ANCHOR_END: vault

-- ANCHOR: vault_use
/-- The type checker computes the balance: `0 + 100 - 30` is `70`. -/
def vault70 : Vault 70 :=
  ((Vault.open "lab").deposit 100).withdraw 30 (by decide)

/-- info: 70 -/
#guard_msgs in
#eval vault70.balance
-- ANCHOR_END: vault_use

-- ANCHOR: overdraw
/--
error: Tactic `decide` proved that the proposition
  30 ≤ 0 + 10
is false
-/
#guard_msgs in
def overdrawn := ((Vault.open "lab").deposit 10).withdraw 30 (by decide)
-- ANCHOR_END: overdraw

-- ANCHOR: runtime
/-- An amount known only at run time: the dependent `if` tests the condition
and, in the `then` branch, hands us a proof `h` of it. -/
def tryWithdraw {b : Nat} (v : Vault b) (amount : Nat) :
    Option (Vault (b - amount)) :=
  if h : amount ≤ b then some (v.withdraw amount h) else none

/-- info: none -/
#guard_msgs in
#eval (tryWithdraw ((Vault.open "lab").deposit 10) 30).map Vault.balance

/-- info: some 20 -/
#guard_msgs in
#eval (tryWithdraw ((Vault.open "lab").deposit 50) 30).map Vault.balance
-- ANCHOR_END: runtime

-- ANCHOR: any_vault
/-- A vault with *some* balance: a dependent pair of the balance and a vault
of that balance. This is how a balance computed at run time is packaged. -/
abbrev AnyVault := (b : Nat) × Vault b

/-- Apply a list of transactions (positive: deposit, negative: withdrawal).
Withdrawals that would overdraw are skipped. -/
def applyAll : AnyVault → List Int → AnyVault
  | v, [] => v
  | ⟨b, v⟩, d :: ds =>
    if d ≥ 0 then
      applyAll ⟨b + d.toNat, v.deposit d.toNat⟩ ds
    else if h : d.natAbs ≤ b then
      applyAll ⟨b - d.natAbs, v.withdraw d.natAbs h⟩ ds
    else
      applyAll ⟨b, v⟩ ds

/-- info: 90 -/
#guard_msgs in
#eval (applyAll ⟨0, Vault.open "lab"⟩ [100, -30, -500, 20]).1
-- ANCHOR_END: any_vault

-- ANCHOR: vault_theorem
/-- Whatever the transactions, the result is a well-formed vault: its type
index *is* its balance, and it is a natural number, so it never went
negative. What we can still prove is how deposits add up. -/
theorem applyAll_deposits (b : Nat) (v : Vault b) (ds : List Nat) :
    (applyAll ⟨b, v⟩ (ds.map Int.ofNat)).1 = b + ds.sum := by
  induction ds generalizing b with
  | nil => simp [applyAll]
  | cons d ds ih =>
    -- a deposit: the `d ≥ 0` branch is taken
    simp only [List.map_cons, applyAll, Int.ofNat_eq_natCast, Int.natCast_nonneg,
      ↓reduceIte, Int.toNat_natCast, List.sum_cons]
    rw [ih]
    omega
-- ANCHOR_END: vault_theorem

end Ch25.Typestate
