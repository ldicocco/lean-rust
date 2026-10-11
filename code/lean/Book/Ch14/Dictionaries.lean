import Book.Ch14.Monoid

/-!
# Chapter 14 · Classes are structures, instances are dictionaries

What the elaborator does with a class: the instance argument `[Monoid α]` is
an ordinary parameter whose type is a structure; `mconcat` written with an
explicit dictionary computes the same function (proved); instance resolution
builds dictionaries from instance declarations (`#synth`, `inferInstance`);
a missing instance is an error; and Lean, unlike Rust, allows several
instances for the same type, chosen by recency and priority.
-/

namespace Ch14

open Monoid

-- ANCHOR: class_is_structure
/--
info: class Ch14.Monoid (α : Type) : Type
number of parameters: 1
fields:
  Ch14.Monoid.empty : α
  Ch14.Monoid.combine : α → α → α
constructor:
  Ch14.Monoid.mk {α : Type} (empty : α) (combine : α → α → α) : Monoid α
-/
#guard_msgs in
#print Monoid

/-- info: @combine : {α : Type} → [self : Monoid α] → α → α → α -/
#guard_msgs in
#check @Monoid.combine

/-- info: @mconcat : {α : Type} → [Monoid α] → List α → α -/
#guard_msgs in
#check @mconcat
-- ANCHOR_END: class_is_structure

-- ANCHOR: explicit_dictionary
/-- `mconcat` after the dictionary-passing translation: the dictionary `d` is
an explicit argument, and every method call reads a field of it. -/
def mconcatExplicit {α : Type} (d : Monoid α) : List α → α
  | [] => d.empty
  | x :: xs => d.combine x (mconcatExplicit d xs)

/-- The translation is faithful: given the instance that resolution would
find, the explicit version computes exactly what `mconcat` computes. -/
theorem mconcatExplicit_eq {α : Type} [inst : Monoid α] (xs : List α) :
    mconcatExplicit inst xs = mconcat xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    -- Goal: inst.combine x (mconcatExplicit inst xs) = x ⋄ mconcat xs
    show inst.combine x (mconcatExplicit inst xs) = x ⋄ mconcat xs
    -- Rewrite with the induction hypothesis; both sides are then identical.
    rw [ih]
-- ANCHOR_END: explicit_dictionary

-- ANCHOR: passing_by_hand
/-- info: 9 -/
#guard_msgs in
#eval mconcat [2, 3, 4]

/-- info: 24 -/
#guard_msgs in
#eval mconcatExplicit ⟨1, (· * ·)⟩ [2, 3, 4]

/-- info: 24 -/
#guard_msgs in
#eval @mconcat Nat ⟨1, (· * ·)⟩ [2, 3, 4]
-- ANCHOR_END: passing_by_hand

-- ANCHOR: synth
/-- info: instMonoidProd -/
#guard_msgs in
#synth Monoid (Nat × List String)

/-- info: @instMonoidProd Nat (List String) instMonoidNat (@instMonoidList String) -/
#guard_msgs in
set_option pp.explicit true in
#synth Monoid (Nat × List String)

-- `inferInstance` asks resolution for a dictionary, as an ordinary term.
/-- info: (5, ["a", "b"]) -/
#guard_msgs in
#eval mconcatExplicit (inferInstance : Monoid (Nat × List String)) [(2, ["a"]), (3, ["b"])]
-- ANCHOR_END: synth

-- ANCHOR: no_instance
/--
error: failed to synthesize
  Monoid Bool

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Monoid Bool

/--
error: failed to synthesize instance of type class
  Monoid Bool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def allReady (flags : List Bool) : Bool := mconcat flags
-- ANCHOR_END: no_instance

-- ANCHOR: several_instances
section Multiplication

/-- A second `Monoid Nat` instance, visible only until the end of this
section. Lean accepts it; Rust would reject it (E0119). -/
local instance natMul : Monoid Nat where
  empty := 1
  combine a b := a * b

-- The most recently declared instance wins: the same expression as above
-- now means a product.
-- ANCHOR: product_eval
/-- info: 24 -/
#guard_msgs in
#eval mconcat [2, 3, 4]
-- ANCHOR_END: product_eval

end Multiplication

-- After the section, the local instance is gone.
/-- info: 9 -/
#guard_msgs in
#eval mconcat [2, 3, 4]

section Priorities

/-- A low-priority instance is tried only after the default-priority ones. -/
local instance (priority := low) natMax : Monoid Nat where
  empty := 0
  combine a b := max a b

/-- info: 9 -/
#guard_msgs in
#eval mconcat [2, 3, 4]

end Priorities

-- `letI` adds an instance for a single expression.
/-- info: 4 -/
#guard_msgs in
#eval
  letI : Monoid Nat := ⟨0, max⟩
  mconcat [2, 3, 4]
-- ANCHOR_END: several_instances

end Ch14
