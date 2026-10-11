import Book.Ch30.Vectors

/-!
# Chapter 30 · Equality as a type

Equality built from scratch as an inductive family, Lean's `Eq`, definitional
versus propositional equality (`n + 0 = n` holds by `rfl`, `0 + n = n` needs a
proof by induction), what this means for the indices of `Vec`, rewriting with
`rw` and transporting values along an equation with `▸`, and decidable
equality: tests whose `true` answer carries a proof.
-/

namespace Ch30

-- ANCHOR: same
/-- Equality from scratch: an inductive family with a single constructor.
There is a proof of `Same a b` only when `a` and `b` are the same. -/
inductive Same {α : Type} : α → α → Prop where
  | refl (a : α) : Same a a
-- ANCHOR_END: same

namespace Same

variable {α β : Type}

-- ANCHOR: same_laws
theorem symm {a b : α} (h : Same a b) : Same b a := by
  cases h          -- `h` can only be `refl a`, so Lean replaces `b` by `a`
  exact refl a     -- goal: Same a a

theorem trans {a b c : α} (hab : Same a b) (hbc : Same b c) : Same a c := by
  cases hab        -- now `b` is `a`
  cases hbc        -- now `c` is `a`
  exact refl a

theorem congrArg (f : α → β) {a b : α} (h : Same a b) : Same (f a) (f b) := by
  cases h
  exact refl (f a)

/-- Transport: whatever holds of `a` holds of anything the same as `a`. -/
theorem subst (P : α → Prop) {a b : α} (h : Same a b) (pa : P a) : P b := by
  cases h
  exact pa

/-- Our `Same` and Lean's `Eq` are interchangeable. -/
theorem iff_eq {a b : α} : Same a b ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; exact refl a
-- ANCHOR_END: same_laws

end Same

-- ANCHOR: print_eq
/--
info: inductive Eq.{u_1} : {α : Sort u_1} → α → α → Prop
number of parameters: 2
constructors:
Eq.refl : ∀ {α : Sort u_1} (a : α), a = a
-/
#guard_msgs in
#print Eq
-- ANCHOR_END: print_eq

-- ANCHOR: defeq
example : 2 + 2 = 4 := rfl                       -- computation on numerals
example (n : ℕ) : n + 0 = n := rfl               -- one step of `Nat.add`
example (n : ℕ) : (fun k => k + 1) n = n + 1 := rfl   -- a β-reduction
example : Vec.three.head = 10 := rfl             -- unfolding our own definitions
-- ANCHOR_END: defeq

-- ANCHOR: zero_add_rfl
/--
error: Type mismatch
  rfl
has type
  ?m.9 = ?m.9
but is expected to have type
  0 + n = n
-/
#guard_msgs in
example (n : ℕ) : 0 + n = n := rfl
-- ANCHOR_END: zero_add_rfl

-- ANCHOR: zero_add_proof
theorem zero_add' (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl                 -- 0 + 0 = 0 is a computation
  | succ k ih =>
    -- ih   : 0 + k = k
    -- goal : 0 + (k + 1) = k + 1
    show (0 + k) + 1 = k + 1    -- the same goal, after one step of `Nat.add`
    rw [ih]                     -- replace `0 + k` by `k`; `rw` then closes `k + 1 = k + 1`
-- ANCHOR_END: zero_add_proof

-- ANCHOR: append_nm_fail
/--
error: Type mismatch
  ys
has type
  Vec α m
but is expected to have type
  Vec α (0 + m)
---
error: Type mismatch
  Vec.cons x (appendNM xs ys)
has type
  Vec α (n✝ + m + 1)
but is expected to have type
  Vec α (n✝ + 1 + m)
-/
#guard_msgs in
def appendNM {α : Type} {n m : ℕ} : Vec α n → Vec α m → Vec α (n + m)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendNM xs ys)
-- ANCHOR_END: append_nm_fail

namespace Vec

variable {α : Type}

-- ANCHOR: append_cast
/-- Concatenation with the length `n + m`: we reuse `append`, whose result has
length `m + n`, and transport it along the equation `m + n = n + m`. -/
def append' {n m : ℕ} (xs : Vec α n) (ys : Vec α m) : Vec α (n + m) :=
  Nat.add_comm m n ▸ xs.append ys
-- ANCHOR_END: append_cast

-- ANCHOR: cast_lemmas
/-- Transport changes the type, not the elements. -/
theorem toList_cast {n m : ℕ} (h : n = m) (v : Vec α n) :
    (h ▸ v : Vec α m).toList = v.toList := by
  subst h      -- replace `m` by `n` everywhere; now `h ▸ v` is just `v`
  rfl

theorem toList_append' {n m : ℕ} (xs : Vec α n) (ys : Vec α m) :
    (xs.append' ys).toList = xs.toList ++ ys.toList := by
  rw [append', toList_cast, toList_append]
-- ANCHOR_END: cast_lemmas

end Vec

-- ANCHOR: decidable
/-- info: true -/
#guard_msgs in
#eval decide (2 + 2 = 4)

inductive Color where
  | red | green | blue
  deriving DecidableEq, Repr

/-- info: false -/
#guard_msgs in
#eval decide (Color.red = Color.blue)

/--
info: inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
-/
#guard_msgs in
#print Decidable
-- ANCHOR_END: decidable

-- ANCHOR: to_vec
/-- From a vector of unknown length to a vector of length `n`. The run-time
test `h : k = n` produces a proof, and the proof changes the type. -/
def SomeVec.toVec? {α : Type} (n : ℕ) : SomeVec α → Option (Vec α n)
  | ⟨k, v⟩ => if h : k = n then some (h ▸ v) else none
-- ANCHOR_END: to_vec

-- ANCHOR: to_vec_eval
/-- info: some [1, 2, 3] -/
#guard_msgs in
#eval ((SomeVec.ofList [1, 2, 3]).toVec? 3).map Vec.toList

/-- info: none -/
#guard_msgs in
#eval ((SomeVec.ofList [1, 2, 3]).toVec? 4).map Vec.toList
-- ANCHOR_END: to_vec_eval

-- ANCHOR: undecidable
/--
error: failed to synthesize
  Decidable (∀ (n : ℕ), n + 0 = n)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : ∀ n : ℕ, n + 0 = n := by decide

/-- A bounded quantifier is decidable: Lean checks the hundred cases. -/
example : ∀ n < 100, 0 + n = n := by decide
-- ANCHOR_END: undecidable

end Ch30
