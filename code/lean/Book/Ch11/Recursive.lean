import Mathlib.Data.Nat.Notation
import Book.Ch11.Iso

/-!
# Chapter 11 · Recursive types

A list type written out by hand, the fixed-point isomorphism
`MyList α ≅ 1 + α × MyList α`, the fold as the elimination principle (with a
proof that it is the *only* function satisfying its two equations), the
recursor Lean generates, an empty recursive type (`μX. X`), and the natural
numbers as a solution of `X ≅ 1 + X`.
-/

namespace Ch11

open Ch11.Iso

-- ANCHOR: mylist
/-- Lists, from scratch: a list is empty, or a head followed by a list. -/
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α
deriving Repr
-- ANCHOR_END: mylist

namespace MyList

variable {α β : Type}

-- ANCHOR: roll
/-- Unfold one layer: a list *is* `1 + α × MyList α`. -/
def unroll : MyList α → Unit ⊕ (α × MyList α)
  | nil => .inl ()
  | cons a as => .inr (a, as)

/-- Fold one layer back. -/
def roll : Unit ⊕ (α × MyList α) → MyList α
  | .inl () => nil
  | .inr (a, as) => cons a as

/-- `MyList α` is a solution of the equation `X ≅ 1 + α × X`. -/
def fixedPoint (α : Type) : MyList α ≅ Unit ⊕ (α × MyList α) where
  toFun := unroll
  invFun := roll
  left_inv xs := by cases xs <;> rfl
  right_inv s := by
    rcases s with ⟨⟨⟩⟩ | ⟨a, as⟩  -- `()` on the left, a pair on the right
    · rfl
    · rfl
-- ANCHOR_END: roll

-- ANCHOR: fold
/-- The fold: give a result for the empty list, and a way to combine a head
with the result for the tail. -/
def fold (n : β) (c : α → β → β) : MyList α → β
  | nil => n
  | cons a as => c a (fold n c as)

def length (xs : MyList α) : ℕ := xs.fold 0 (fun _ k => k + 1)
def sum (xs : MyList ℕ) : ℕ := xs.fold 0 (fun a s => a + s)
def map (f : α → β) (xs : MyList α) : MyList β :=
  xs.fold nil (fun a bs => cons (f a) bs)
-- ANCHOR_END: fold

-- ANCHOR: fold_eval
/-- info: 3 -/
#guard_msgs in
#eval (cons 4 (cons 5 (cons 6 nil))).length

/-- info: 15 -/
#guard_msgs in
#eval (cons 4 (cons 5 (cons 6 nil))).sum

/-- info: Ch11.MyList.cons 40 (Ch11.MyList.cons 50 (Ch11.MyList.nil)) -/
#guard_msgs in
#eval (cons 4 (cons 5 nil)).map (· * 10)
-- ANCHOR_END: fold_eval

-- ANCHOR: fold_unique
/-- Any function `h` that satisfies the two equations of `fold` *is* `fold`.
This is what "the fold is the elimination principle of lists" means. -/
theorem fold_unique (n : β) (c : α → β → β) (h : MyList α → β)
    (h_nil : h nil = n) (h_cons : ∀ a as, h (cons a as) = c a (h as)) :
    ∀ xs, h xs = xs.fold n c := by
  intro xs
  induction xs with
  | nil =>
    -- Goal: h nil = fold n c nil, and the right side computes to n.
    rw [h_nil]
    rfl
  | cons a as ih =>
    -- ih   : h as = fold n c as
    -- Goal : h (cons a as) = fold n c (cons a as)
    rw [h_cons, ih]
    rfl

/-- Folding with the constructors themselves rebuilds the list. -/
theorem fold_nil_cons (xs : MyList α) : xs.fold nil cons = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    show cons a (as.fold nil cons) = cons a as
    rw [ih]
-- ANCHOR_END: fold_unique

-- ANCHOR: map_laws
/-- Two consequences of uniqueness, proved by induction: `map` preserves the
length, and mapping the identity does nothing. -/
theorem length_map (f : α → β) (xs : MyList α) : (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    show (as.map f).length + 1 = as.length + 1
    rw [ih]

theorem map_id (xs : MyList α) : xs.map (fun a => a) = xs :=
  fold_nil_cons xs
-- ANCHOR_END: map_laws

end MyList

-- ANCHOR: rec
/-- The recursor that Lean generated for `MyList`, used to prove a property `P`
of every list: prove it for `nil`, and prove it for `cons a as` assuming it for
`as`. This is the induction principle that the `induction` tactic applies. -/
example {α : Type} (P : MyList α → Prop)
    (h_nil : P .nil) (h_cons : ∀ a as, P as → P (.cons a as)) : ∀ xs, P xs :=
  fun xs => MyList.rec h_nil h_cons xs

/-- The same recursor, used to compute a value of a fixed type `β`, is the fold. -/
example {α β : Type} (n : β) (c : α → β → β) (xs : MyList α) :
    MyList.rec (motive := fun _ => β) n (fun a _ r => c a r) xs = xs.fold n c := by
  induction xs with
  | nil => rfl
  | cons a as ih => exact congrArg (c a) ih
-- ANCHOR_END: rec

-- ANCHOR: loop
/-- `μX. X`: a type whose only constructor needs a value of the type itself. -/
inductive Loop where
  | next : Loop → Loop

/-- No value of `Loop` can ever be built: by induction, every `Loop` gives a
proof of `False`. -/
theorem Loop.elim (l : Loop) : False := by
  induction l with
  | next _ ih => exact ih

/-- So `Loop` is isomorphic to the empty type. -/
def loopEmpty : Loop ≅ Empty where
  toFun l := (Loop.elim l).elim
  invFun e := nomatch e
  left_inv l := (Loop.elim l).elim
  right_inv e := nomatch e
-- ANCHOR_END: loop

-- ANCHOR: nat_fixed_point
/-- `ℕ ≅ 1 + ℕ`: the natural numbers solve `X ≅ 1 + X`. In arithmetic,
`n = 1 + n` has no solution; for infinite types it does, so the algebra of
types cannot be "cancelled" like the algebra of numbers. -/
def natFixedPoint : ℕ ≅ Unit ⊕ ℕ where
  toFun
    | 0 => .inl ()
    | n + 1 => .inr n
  invFun
    | .inl () => 0
    | .inr n => n + 1
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with ⟨⟨⟩⟩ | n
    · rfl
    · rfl
-- ANCHOR_END: nat_fixed_point

end Ch11
