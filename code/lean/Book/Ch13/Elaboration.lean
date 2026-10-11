/-!
# Chapter 13 · Lean's elaborator

How Lean fills in what you leave out: metavariables solved by unification,
default instances for numerals, the errors you get when nothing determines a
type (Lean's analogues of Rust's E0282), why `let` is not polymorphic,
unification up to computation, higher-order patterns, holes `_` and `?_`,
type ascriptions and `show`.
-/

namespace Ch13.Elab

-- ANCHOR: numerals
/-- info: fun x => x + 1 : Nat → Nat -/
#guard_msgs in
#check fun x => x + 1

/-- info: fun x => x + 1 : Int → Int -/
#guard_msgs in
#check fun (x : Int) => x + 1
-- ANCHOR_END: numerals

-- ANCHOR: explicit
set_option pp.explicit true in
/-- info: @id Bool true : Bool -/
#guard_msgs in
#check id true
-- ANCHOR_END: explicit

-- ANCHOR: binder_failed
/--
error: Failed to infer type of binder `x`
---
error: Failed to infer type of definition `idFun`
-/
#guard_msgs in
def idFun := fun x => x
-- ANCHOR_END: binder_failed

-- ANCHOR: empty_list
/--
error: don't know how to synthesize implicit argument `α`
  @List.nil ?m.3
context:
⊢ Type u_1
---
error: Failed to infer type of definition `emptyList`
-/
#guard_msgs in
def emptyList := []

def emptyNats : List Nat := []
-- ANCHOR_END: empty_list

-- ANCHOR: auto_bound
/-- A polymorphic definition: `α` is bound automatically, as an implicit
argument. -/
def myId (x : α) : α := x

/-- info: @myId : {α : Sort u_1} → α → α -/
#guard_msgs in
#check @myId

example : Nat × Bool := (myId 1, myId true)
-- ANCHOR_END: auto_bound

-- ANCHOR: let_mono
/--
error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  Nat
in the application
  f true
-/
#guard_msgs in
example : Nat × Bool :=
  let f := fun x => x
  (f 1, f true)

/-- With an explicit polymorphic type, the local function is fine. -/
example : Nat × Bool :=
  let f : {α : Type} → α → α := fun x => x
  (f 1, f true)
-- ANCHOR_END: let_mono

-- ANCHOR: field
/--
error: Invalid field notation: Type of
  x
is not known; cannot resolve field `succ`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Fin.succ`
  • `Nat.succ`
  • `Std.PRange.succ`
-/
#guard_msgs in
def succAll := fun x => x.succ

/-- info: fun x => x.succ : Nat → Nat -/
#guard_msgs in
#check (fun x => x.succ : Nat → Nat)
-- ANCHOR_END: field

-- ANCHOR: holes
/--
error: don't know how to synthesize placeholder for argument `a`
context:
⊢ Nat
-/
#guard_msgs in
def sevens : List Nat := List.replicate 3 _

/-- `?_` is a hole too, but a *named goal*: tactics fill it in later. -/
def sevens' : List Nat := by
  refine List.replicate 3 ?_
  exact 7

/-- info: [7, 7, 7] -/
#guard_msgs in
#eval sevens'
-- ANCHOR_END: holes

-- ANCHOR: defeq
/-- Unification computes: `?n + 0` reduces to `?n`, so `?n := 5`. -/
example : ∃ n : Nat, n + 0 = 5 := ⟨_, rfl⟩

/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.15 = ?m.15
but is expected to have type
  0 + ?m.13 = 5
in the application
  Exists.intro ?m.13 rfl
-/
#guard_msgs in
example : ∃ n : Nat, 0 + n = 5 := ⟨_, rfl⟩
-- ANCHOR_END: defeq

-- ANCHOR: higher_order
/-- A higher-order *pattern*: `?f x = x + 1` with `x` a bound variable has
exactly one solution, `?f := fun x => x + 1`. -/
example : ∃ f : Nat → Nat, ∀ x, f x = x + 1 := ⟨_, fun _ => rfl⟩

/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.11 = ?m.11
but is expected to have type
  ?m.9 3 = 6
in the application
  Exists.intro ?m.9 rfl
-/
#guard_msgs in
example : ∃ f : Nat → Nat, f 3 = 6 := ⟨_, rfl⟩
-- ANCHOR_END: higher_order

-- ANCHOR: ascription
/-- info: -1 -/
#guard_msgs in
#eval (1 - 2 : Int)

/-- info: 0 -/
#guard_msgs in
#eval ((1 - 2 : Nat) : Int)

/-- info: ↑(1 - 2) : Int -/
#guard_msgs in
#check ((1 - 2 : Nat) : Int)
-- ANCHOR_END: ascription

-- ANCHOR: show
example (n : Nat) : n + 0 = n := by
  show n = n      -- accepted: `n + 0` computes to `n`
  rfl

/--
error: 'show' tactic failed, pattern
  n = n
is not definitionally equal to target
  0 + n = n
-/
#guard_msgs in
example (n : Nat) : 0 + n = n := by
  show n = n
  rfl
-- ANCHOR_END: show

end Ch13.Elab
