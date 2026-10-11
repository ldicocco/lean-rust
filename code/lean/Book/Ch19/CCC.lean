import Book.Ch16.Category
import Mathlib.Order.Heyting.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Chapter 19 · Cartesian closed categories

Built on the book's `Category` class (Chapter 16): terminal objects, binary
products and exponentials, each given by its universal property; the class
`CartesianClosed`; currying as a natural bijection of hom-sets (the first
adjunction); the instance for Lean's types; and every Heyting algebra as a
thin cartesian closed category, with residuation recovered from currying.
-/

namespace Ch19

open Ch16

universe u

-- ANCHOR: terminal
/-- A terminal object: exactly one morphism into it from every object. -/
class HasTerminal (Obj : Type u) [Category Obj] where
  one : Obj
  toOne : (a : Obj) → (a ⟶ one)
  toOne_unique : ∀ {a : Obj} (f : a ⟶ one), f = toOne a
-- ANCHOR_END: terminal

-- ANCHOR: products
/-- Binary products, by their universal property: projections `fst` and
`snd`, and for every pair of morphisms `f : x ⟶ a`, `g : x ⟶ b` a morphism
`pair f g : x ⟶ a ⨯ b` that is the only one with `fst ⊚ _ = f` and
`snd ⊚ _ = g`. -/
class HasProducts (Obj : Type u) [Category Obj] where
  /-- The product object `a ⨯ b`. -/
  prod : Obj → Obj → Obj
  fst : {a b : Obj} → (prod a b ⟶ a)
  snd : {a b : Obj} → (prod a b ⟶ b)
  pair : {x a b : Obj} → (x ⟶ a) → (x ⟶ b) → (x ⟶ prod a b)
  fst_pair : ∀ {x a b : Obj} (f : x ⟶ a) (g : x ⟶ b), fst ⊚ pair f g = f
  snd_pair : ∀ {x a b : Obj} (f : x ⟶ a) (g : x ⟶ b), snd ⊚ pair f g = g
  pair_unique : ∀ {x a b : Obj} (h : x ⟶ prod a b), pair (fst ⊚ h) (snd ⊚ h) = h

@[inherit_doc] scoped infixr:35 " ⨯ " => HasProducts.prod
-- ANCHOR_END: products

open HasTerminal HasProducts

section Products

variable {Obj : Type u} [Category Obj] [HasProducts Obj]

-- ANCHOR: product_lemmas
/-- Uniqueness, in the form used most: a morphism into a product is
determined by its two projections. -/
theorem pair_eq {x a b : Obj} {f : x ⟶ a} {g : x ⟶ b} {h : x ⟶ a ⨯ b}
    (h₁ : fst ⊚ h = f) (h₂ : snd ⊚ h = g) : h = pair f g := by
  rw [← pair_unique h, h₁, h₂]

/-- Precomposing a pair precomposes both components. -/
theorem pair_comp {y x a b : Obj} (f : x ⟶ a) (g : x ⟶ b) (h : y ⟶ x) :
    pair f g ⊚ h = pair (f ⊚ h) (g ⊚ h) :=
  pair_eq (by rw [Category.assoc, fst_pair]) (by rw [Category.assoc, snd_pair])

/-- `pair fst snd` is the identity of the product. -/
theorem pair_fst_snd {a b : Obj} : pair fst snd = Category.id (a ⨯ b) := by
  have h := pair_unique (Category.id (a ⨯ b))
  rw [Category.comp_id, Category.comp_id] at h
  exact h
-- ANCHOR_END: product_lemmas

-- ANCHOR: prod_map
/-- The product of two morphisms, `f × g`, acting on each component. -/
def prodMap {a b c d : Obj} (f : a ⟶ c) (g : b ⟶ d) : a ⨯ b ⟶ c ⨯ d :=
  pair (f ⊚ fst) (g ⊚ snd)

theorem prodMap_comp {a b c d e k : Obj} (f : c ⟶ e) (g : d ⟶ k) (h : a ⟶ c)
    (m : b ⟶ d) : prodMap f g ⊚ prodMap h m = prodMap (f ⊚ h) (g ⊚ m) := by
  unfold prodMap
  rw [pair_comp, ← Category.assoc, fst_pair, ← Category.assoc, snd_pair,
    Category.assoc, Category.assoc]

theorem prodMap_comp_id {a b c d : Obj} (g : c ⟶ d) (h : a ⟶ c) :
    prodMap (g ⊚ h) (Category.id b) = prodMap g (Category.id b) ⊚ prodMap h (Category.id b) := by
  rw [prodMap_comp, Category.id_comp]

/-- A pair splits into "keep the second component, then apply `h` to the
first". -/
theorem pair_eq_prodMap {x a b : Obj} (h : x ⟶ a) (g : x ⟶ b) :
    pair h g = prodMap h (Category.id b) ⊚ pair (Category.id x) g := by
  unfold prodMap
  rw [pair_comp, ← Category.assoc, fst_pair, Category.comp_id, ← Category.assoc,
    snd_pair, Category.id_comp]
-- ANCHOR_END: prod_map

-- ANCHOR: diagonal
/-- The diagonal `a ⟶ a ⨯ a`: every object of a category with products can be
copied. -/
def diag (a : Obj) : a ⟶ a ⨯ a := pair (Category.id a) (Category.id a)

/-- The diagonal is natural: copying and then applying `f` to both copies is
the same as applying `f` and then copying. -/
theorem diag_natural {a b : Obj} (f : a ⟶ b) : prodMap f f ⊚ diag a = diag b ⊚ f := by
  unfold diag prodMap
  rw [pair_comp, pair_comp, ← Category.assoc, fst_pair, ← Category.assoc, snd_pair,
    Category.comp_id, Category.id_comp]

/-- Copying and then forgetting one copy does nothing. -/
theorem fst_diag (a : Obj) : fst ⊚ diag a = Category.id a := fst_pair _ _
-- ANCHOR_END: diagonal

end Products

-- ANCHOR: ccc
/-- A cartesian closed category: a terminal object, binary products, and for
all objects `b`, `c` an exponential `b ⟹ c` (the object of morphisms from `b`
to `c`) with an evaluation morphism, such that every `f : a ⨯ b ⟶ c` factors
through `eval` by exactly one `curry f : a ⟶ (b ⟹ c)`. -/
class CartesianClosed (Obj : Type u) [Category Obj] [HasTerminal Obj]
    [HasProducts Obj] where
  /-- The exponential object `b ⟹ c`. -/
  exp : Obj → Obj → Obj
  eval : {b c : Obj} → (exp b c ⨯ b ⟶ c)
  curry : {a b c : Obj} → (a ⨯ b ⟶ c) → (a ⟶ exp b c)
  eval_curry : ∀ {a b c : Obj} (f : a ⨯ b ⟶ c),
    eval ⊚ prodMap (curry f) (Category.id b) = f
  curry_unique : ∀ {a b c : Obj} (g : a ⟶ exp b c),
    curry (eval ⊚ prodMap g (Category.id b)) = g

@[inherit_doc] scoped infixr:30 " ⟹ " => CartesianClosed.exp
-- ANCHOR_END: ccc

open CartesianClosed

section Closed

variable {Obj : Type u} [Category Obj] [HasTerminal Obj] [HasProducts Obj]
  [CartesianClosed Obj]

-- ANCHOR: uncurry
/-- `uncurry g`: evaluate after applying `g` to the first component. -/
def uncurry {a b c : Obj} (g : a ⟶ (b ⟹ c)) : a ⨯ b ⟶ c :=
  eval ⊚ prodMap g (Category.id b)

theorem uncurry_curry {a b c : Obj} (f : a ⨯ b ⟶ c) : uncurry (curry f) = f :=
  eval_curry f

theorem curry_uncurry {a b c : Obj} (g : a ⟶ (b ⟹ c)) : curry (uncurry g) = g :=
  curry_unique g

/-- Currying is a bijection between the two hom-sets. -/
def curryEquiv (a b c : Obj) : (a ⨯ b ⟶ c) ≃ (a ⟶ (b ⟹ c)) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
-- ANCHOR_END: uncurry

-- ANCHOR: curry_natural
/-- The bijection is natural in `a`: currying commutes with precomposition.
Together with `curryEquiv`, this is the statement that `(· ⨯ b)` is left
adjoint to `(b ⟹ ·)`. -/
theorem curry_natural {x a b c : Obj} (f : a ⨯ b ⟶ c) (h : x ⟶ a) :
    curry (f ⊚ prodMap h (Category.id b)) = curry f ⊚ h := by
  -- Write the right-hand side as `curry (uncurry (curry f ⊚ h))`...
  conv_rhs => rw [← curry_unique (curry f ⊚ h)]
  -- ...and compare the arguments of `curry`.
  rw [prodMap_comp_id, Category.assoc, eval_curry]

/-- The categorical β-law: evaluating a curried morphism at an argument. -/
theorem eval_pair_curry {x b c : Obj} (f : x ⨯ b ⟶ c) (g : x ⟶ b) :
    eval ⊚ pair (curry f) g = f ⊚ pair (Category.id x) g := by
  rw [pair_eq_prodMap, Category.assoc, eval_curry]
-- ANCHOR_END: curry_natural

end Closed

/-! ## Lean's types form a cartesian closed category -/

-- ANCHOR: type_ccc
instance : HasTerminal Type where
  one := Unit
  toOne _ := fun _ => ()
  toOne_unique _ := rfl

instance : HasProducts Type where
  prod a b := a × b
  fst := fun p => p.1
  snd := fun p => p.2
  pair f g := fun x => (f x, g x)
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl
  pair_unique _ := rfl

instance : CartesianClosed Type where
  exp b c := b → c
  eval := fun p => p.1 p.2
  curry f := fun a b => f (a, b)
  eval_curry _ := rfl
  curry_unique _ := rfl
-- ANCHOR_END: type_ccc

-- ANCHOR: type_examples
/-- In `Type`, `curry` is ordinary currying. -/
example : (curry (fun p : ℕ × ℕ => p.1 + p.2) : ℕ ⟶ (ℕ ⟹ ℕ)) 2 3 = 5 := rfl

/-- And the diagonal is `fun x => (x, x)`. -/
example : (diag ℕ : ℕ ⟶ ℕ ⨯ ℕ) 7 = (7, 7) := rfl
-- ANCHOR_END: type_examples

/-! ## Heyting algebras are thin cartesian closed categories -/

-- ANCHOR: thin
/-- A copy of a preordered type, so that the category structure below does not
attach itself to the type `α` everywhere. -/
structure Thin (α : Type) where
  val : α

/-- A preorder as a category: one morphism `a ⟶ b` exactly when `a ≤ b`.
Every diagram commutes, because any two morphisms with the same ends are
equal (they are proofs of the same `≤`). -/
instance thinCategory (α : Type) [Preorder α] : Category (Thin α) where
  Hom a b := PLift (a.val ≤ b.val)
  id a := ⟨le_refl a.val⟩
  comp g f := ⟨le_trans f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
-- ANCHOR_END: thin

section Heyting

-- ANCHOR: heyting_ccc
variable (α : Type) [HeytingAlgebra α]

/-- Top is terminal: everything is `≤ ⊤`. -/
instance : HasTerminal (Thin α) where
  one := ⟨⊤⟩
  toOne _ := ⟨le_top⟩
  toOne_unique _ := rfl

/-- Meet is the product: `x ≤ a ⊓ b` exactly when `x ≤ a` and `x ≤ b`. -/
instance : HasProducts (Thin α) where
  prod a b := ⟨a.val ⊓ b.val⟩
  fst := ⟨inf_le_left⟩
  snd := ⟨inf_le_right⟩
  pair f g := ⟨le_inf f.down g.down⟩
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl
  pair_unique _ := rfl

/-- Heyting implication is the exponential: `eval` is modus ponens, `curry` is
one direction of residuation. -/
instance : CartesianClosed (Thin α) where
  exp b c := ⟨b.val ⇨ c.val⟩
  eval := ⟨himp_inf_le⟩
  curry f := ⟨le_himp_iff.mpr f.down⟩
  eval_curry _ := rfl
  curry_unique _ := rfl
-- ANCHOR_END: heyting_ccc

end Heyting

-- ANCHOR: residuation
/-- Residuation, `a ⊓ b ≤ c ↔ a ≤ b ⇨ c`, read off from the cartesian closed
structure: it is `curry` and `uncurry` in a category where morphisms are
proofs of `≤`. -/
theorem residuation {α : Type} [HeytingAlgebra α] (a b c : α) :
    a ⊓ b ≤ c ↔ a ≤ b ⇨ c := by
  constructor
  · intro h
    -- `h` is a morphism `a ⨯ b ⟶ c` of the thin category; curry it.
    let f : (Thin.mk a ⨯ Thin.mk b : Thin α) ⟶ Thin.mk c := ⟨h⟩
    exact (curry f).down
  · intro h
    -- `h` is a morphism `a ⟶ (b ⟹ c)`; uncurry it.
    let g : (Thin.mk a : Thin α) ⟶ (Thin.mk b ⟹ Thin.mk c) := ⟨h⟩
    exact (uncurry g).down

/-- In `Prop`, the exponential is implication and `eval` is modus ponens. -/
example (p q : Prop) : (p → q) ∧ p → q :=
  (eval : (Thin.mk p ⟹ Thin.mk q) ⨯ Thin.mk p ⟶ Thin.mk q).down
-- ANCHOR_END: residuation

end Ch19
