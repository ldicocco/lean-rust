/-!
# Chapter 25 · Session types, briefly

A session type describes a whole conversation. Its dual describes the same
conversation from the other side; duality is an involution. Processes are
indexed by their session type, and two processes with dual types can always
talk to completion: `talk` is a total function, with no case for a mismatch.
-/

namespace Ch25.Session

-- ANCHOR: session
/-- The types of the messages. -/
inductive Ty where
  | nat | bool
  deriving DecidableEq

/-- The Lean type of a message of type `t`. -/
abbrev Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool

inductive Session where
  | send (t : Ty) (k : Session)   -- send a `t`, continue as `k`
  | recv (t : Ty) (k : Session)   -- receive a `t`, continue as `k`
  | done
  deriving DecidableEq

def Session.dual : Session → Session
  | .send t k => .recv t k.dual
  | .recv t k => .send t k.dual
  | .done => .done
-- ANCHOR_END: session

-- ANCHOR: dual_dual
/-- Duality is an involution: the other side of the other side is you. -/
theorem Session.dual_dual (s : Session) : s.dual.dual = s := by
  induction s with
  | send t k ih => simp [dual, ih]
  | recv t k ih => simp [dual, ih]
  | done => rfl
-- ANCHOR_END: dual_dual

-- ANCHOR: proc
/-- A process that follows session `s`. Sending needs a value of the right
type; receiving needs a continuation for every value that may arrive. -/
inductive Proc : Session → Type where
  | send {t : Ty} {k : Session} : t.denote → Proc k → Proc (.send t k)
  | recv {t : Ty} {k : Session} : (t.denote → Proc k) → Proc (.recv t k)
  | done : Proc .done

def Ty.show : (t : Ty) → t.denote → String
  | .nat, n => toString n
  | .bool, b => toString b

/-- Run two processes with dual sessions against each other, recording the
messages. There are only three cases: the types rule out every mismatch
(both sending, both receiving, one finished early), and the recursion is
structural, so the conversation always completes. -/
def talk : {s : Session} → Proc s → Proc s.dual → List String
  | .send t _, .send v p, .recv f => s!"→ {t.show v}" :: talk p (f v)
  | .recv t _, .recv f, .send v q => s!"← {t.show v}" :: talk (f v) q
  | .done, .done, .done => []
-- ANCHOR_END: proc

-- ANCHOR: example
/-- The client's protocol: send a sensor number, receive whether it is
in service. -/
def Query : Session := .send .nat (.recv .bool .done)

def client : Proc Query :=
  .send (7 : Nat) (.recv fun _inService => .done)

/-- The server follows the dual protocol: receive, then send. -/
def server : Proc Query.dual :=
  .recv fun (sensor : Nat) => .send (decide (sensor < 10)) .done

/-- info: ["→ 7", "← true"] -/
#guard_msgs in
#eval talk client server
-- ANCHOR_END: example

end Ch25.Session
