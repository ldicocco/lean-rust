import Book.Ch16.Examples

/-!
# Chapter 16 · Universal properties

Terminal and initial objects, products and coproducts, defined by their
universal properties in any category of the book's `Category` class. We prove
that `Unit`, `Empty`, `α × β` and `α ⊕ β` have these properties in the category
of types, that the same definitions give `min`/`max` in `ℕ` and `∧`/`∨` in
`Prop`, that such objects are unique up to unique isomorphism, and that
duality (the opposite category) turns one notion into the other.
-/

namespace Ch16

universe u

open Category

/-! ## Terminal and initial objects -/

-- ANCHOR: terminal
/-- `t` is terminal: from every object there is exactly one morphism to `t`. -/
structure IsTerminal {Obj : Type u} [Category Obj] (t : Obj) where
  /-- The morphism from `a` to `t`. -/
  arrow : (a : Obj) → a ⟶ t
  /-- It is the only one. -/
  unique : ∀ {a : Obj} (f : a ⟶ t), f = arrow a

/-- `i` is initial: to every object there is exactly one morphism from `i`. -/
structure IsInitial {Obj : Type u} [Category Obj] (i : Obj) where
  /-- The morphism from `i` to `a`. -/
  arrow : (a : Obj) → i ⟶ a
  /-- It is the only one. -/
  unique : ∀ {a : Obj} (f : i ⟶ a), f = arrow a
-- ANCHOR_END: terminal

-- ANCHOR: unit_empty
/-- `Unit` is terminal in the category of types. -/
def unitTerminal : IsTerminal Unit where
  arrow _ := fun _ => ()
  unique _ := by
    funext x           -- compare `f` and `fun _ => ()` on every input `x`
    rfl                -- both give `()`: `Unit` has only one value

/-- `Empty` is initial in the category of types. -/
def emptyInitial : IsInitial Empty where
  arrow _ := fun e => nomatch e
  unique f := by
    funext e           -- compare the two functions on every `e : Empty`...
    nomatch e          -- ...of which there are none
-- ANCHOR_END: unit_empty

-- ANCHOR: nat_terminal
/-- In `ℕ` ordered by `≤`, `0` is initial... -/
def zeroInitial : IsInitial (0 : ℕ) where
  arrow n := ⟨Nat.zero_le n⟩
  unique _ := preorder_thin _ _

/-- ...but there is no terminal object: no number is above every number. -/
theorem nat_no_terminal (n : ℕ) (h : IsTerminal n) : False := by
  have hle : n + 1 ≤ n := (h.arrow (n + 1)).down
  omega
-- ANCHOR_END: nat_terminal

-- ANCHOR: terminal_unique
/-- Two morphisms into a terminal object are always equal. -/
theorem IsTerminal.hom_ext {Obj : Type u} [Category Obj] {t a : Obj}
    (ht : IsTerminal t) (f g : a ⟶ t) : f = g := by
  rw [ht.unique f, ht.unique g]

/-- Terminal objects are unique up to isomorphism... -/
def IsTerminal.iso {Obj : Type u} [Category Obj] {t₁ t₂ : Obj}
    (h₁ : IsTerminal t₁) (h₂ : IsTerminal t₂) : t₁ ≅ t₂ where
  hom := h₂.arrow t₁
  inv := h₁.arrow t₂
  inv_hom := h₁.hom_ext _ _   -- both sides are morphisms `t₁ ⟶ t₁`
  hom_inv := h₂.hom_ext _ _   -- both sides are morphisms `t₂ ⟶ t₂`

/-- ...and the isomorphism is unique: there is only one morphism `t₁ ⟶ t₂`. -/
theorem IsTerminal.iso_unique {Obj : Type u} [Category Obj] {t₁ t₂ : Obj}
    (h₁ : IsTerminal t₁) (h₂ : IsTerminal t₂) (i : t₁ ≅ t₂) :
    i.hom = (h₁.iso h₂).hom :=
  h₂.hom_ext _ _
-- ANCHOR_END: terminal_unique

/-! ## Products -/

-- ANCHOR: product
/-- `p`, with projections `fst` and `snd`, is a product of `a` and `b`: every
pair of morphisms `f : x ⟶ a`, `g : x ⟶ b` factors through `p` in exactly one
way. -/
structure IsProduct {Obj : Type u} [Category Obj] {a b p : Obj}
    (fst : p ⟶ a) (snd : p ⟶ b) where
  /-- The morphism into the product built from `f` and `g`. -/
  lift : {x : Obj} → (x ⟶ a) → (x ⟶ b) → (x ⟶ p)
  /-- Projecting the lift on the first component gives back `f`. -/
  fst_lift : ∀ {x : Obj} (f : x ⟶ a) (g : x ⟶ b), fst ⊚ lift f g = f
  /-- Projecting the lift on the second component gives back `g`. -/
  snd_lift : ∀ {x : Obj} (f : x ⟶ a) (g : x ⟶ b), snd ⊚ lift f g = g
  /-- Any morphism with these two properties is the lift. -/
  uniq : ∀ {x : Obj} (f : x ⟶ a) (g : x ⟶ b) (h : x ⟶ p),
    fst ⊚ h = f → snd ⊚ h = g → h = lift f g
-- ANCHOR_END: product

-- ANCHOR: pair_product
/-- The pair type `α × β`, with `Prod.fst` and `Prod.snd`, is a product in the
category of types. -/
def pairIsProduct (α β : Type) :
    IsProduct (Obj := Type) (Prod.fst : α × β → α) Prod.snd where
  lift f g := fun x => (f x, g x)
  fst_lift _ _ := rfl
  snd_lift _ _ := rfl
  uniq f g h hf hg := by
    -- hf : Prod.fst ⊚ h = f      hg : Prod.snd ⊚ h = g
    funext x
    -- Goal: h x = (f x, g x). Two pairs are equal if their components are.
    apply Prod.ext
    · exact congrFun hf x      -- (h x).1 = f x
    · exact congrFun hg x      -- (h x).2 = g x
-- ANCHOR_END: pair_product

-- ANCHOR: pair_lift_eval
/-- The lift of two functions runs both on the same input. -/
def squareAndLabel : ℕ ⟶ ℕ × String :=
  (pairIsProduct ℕ String).lift (fun n => n * n) (fun n => s!"#{n}")

/-- info: (49, "#7") -/
#guard_msgs in
#eval squareAndLabel 7
-- ANCHOR_END: pair_lift_eval

-- ANCHOR: product_unique
/-- Products are unique up to isomorphism: if `p` and `q` are both products of
`a` and `b`, the lifts of each other's projections are inverse to each other. -/
def IsProduct.iso {Obj : Type u} [Category Obj] {a b p q : Obj}
    {fst : p ⟶ a} {snd : p ⟶ b} {fst' : q ⟶ a} {snd' : q ⟶ b}
    (P : IsProduct fst snd) (Q : IsProduct fst' snd') : p ≅ q where
  hom := Q.lift fst snd
  inv := P.lift fst' snd'
  inv_hom := by
    -- Both `P.lift fst' snd' ⊚ Q.lift fst snd` and `id p` are lifts of
    -- `fst` and `snd` through `p`, so both are equal to `P.lift fst snd`.
    have h₁ : P.lift fst' snd' ⊚ Q.lift fst snd = P.lift fst snd :=
      P.uniq _ _ _
        (by rw [Category.assoc, P.fst_lift, Q.fst_lift])
        (by rw [Category.assoc, P.snd_lift, Q.snd_lift])
    have h₂ : Category.id p = P.lift fst snd :=
      P.uniq _ _ _ (Category.comp_id fst) (Category.comp_id snd)
    rw [h₁, h₂]
  hom_inv := by
    -- The same argument with the roles of `p` and `q` exchanged.
    have h₁ : Q.lift fst snd ⊚ P.lift fst' snd' = Q.lift fst' snd' :=
      Q.uniq _ _ _
        (by rw [Category.assoc, Q.fst_lift, P.fst_lift])
        (by rw [Category.assoc, Q.snd_lift, P.snd_lift])
    have h₂ : Category.id q = Q.lift fst' snd' :=
      Q.uniq _ _ _ (Category.comp_id fst') (Category.comp_id snd')
    rw [h₁, h₂]

/-- The isomorphism commutes with the projections. -/
theorem IsProduct.iso_fst {Obj : Type u} [Category Obj] {a b p q : Obj}
    {fst : p ⟶ a} {snd : p ⟶ b} {fst' : q ⟶ a} {snd' : q ⟶ b}
    (P : IsProduct fst snd) (Q : IsProduct fst' snd') :
    fst' ⊚ (P.iso Q).hom = fst :=
  Q.fst_lift fst snd
-- ANCHOR_END: product_unique

/-! ## Coproducts -/

-- ANCHOR: coproduct
/-- `s`, with injections `inl` and `inr`, is a coproduct of `a` and `b`: every
pair of morphisms `f : a ⟶ x`, `g : b ⟶ x` factors through `s` in exactly one
way. The same definition as `IsProduct`, with every arrow reversed. -/
structure IsCoproduct {Obj : Type u} [Category Obj] {a b s : Obj}
    (inl : a ⟶ s) (inr : b ⟶ s) where
  /-- The morphism out of the coproduct built from `f` and `g`. -/
  desc : {x : Obj} → (a ⟶ x) → (b ⟶ x) → (s ⟶ x)
  /-- On the left injection, the desc behaves like `f`. -/
  desc_inl : ∀ {x : Obj} (f : a ⟶ x) (g : b ⟶ x), desc f g ⊚ inl = f
  /-- On the right injection, the desc behaves like `g`. -/
  desc_inr : ∀ {x : Obj} (f : a ⟶ x) (g : b ⟶ x), desc f g ⊚ inr = g
  /-- Any morphism with these two properties is the desc. -/
  uniq : ∀ {x : Obj} (f : a ⟶ x) (g : b ⟶ x) (h : s ⟶ x),
    h ⊚ inl = f → h ⊚ inr = g → h = desc f g
-- ANCHOR_END: coproduct

-- ANCHOR: sum_coproduct
/-- The sum type `α ⊕ β`, with `Sum.inl` and `Sum.inr`, is a coproduct in the
category of types. -/
def sumIsCoproduct (α β : Type) :
    IsCoproduct (Obj := Type) (Sum.inl : α → α ⊕ β) Sum.inr where
  desc f g := fun s => match s with
    | .inl a => f a
    | .inr b => g b
  desc_inl _ _ := rfl
  desc_inr _ _ := rfl
  uniq f g h hf hg := by
    -- hf : h ⊚ Sum.inl = f      hg : h ⊚ Sum.inr = g
    funext s
    cases s with                        -- a value of `α ⊕ β` is `inl a` or `inr b`
    | inl a => exact congrFun hf a      -- h (inl a) = f a
    | inr b => exact congrFun hg b      -- h (inr b) = g b
-- ANCHOR_END: sum_coproduct

/-! ## The same definitions in other categories -/

-- ANCHOR: min_max
/-- In `ℕ` ordered by `≤`, the candidate projections out of `min a b`... -/
def minFst (a b : ℕ) : min a b ⟶ a := ⟨Nat.min_le_left a b⟩
def minSnd (a b : ℕ) : min a b ⟶ b := ⟨Nat.min_le_right a b⟩

/-- ...make `min a b` a product of `a` and `b`. -/
def minIsProduct (a b : ℕ) : IsProduct (minFst a b) (minSnd a b) where
  lift f g := ⟨Nat.le_min.mpr ⟨f.down, g.down⟩⟩   -- x ≤ a and x ≤ b give x ≤ min a b
  fst_lift _ _ := preorder_thin _ _
  snd_lift _ _ := preorder_thin _ _
  uniq _ _ _ _ _ := preorder_thin _ _

/-- Dually, `max a b` is a coproduct. -/
def maxInl (a b : ℕ) : a ⟶ max a b := ⟨Nat.le_max_left a b⟩
def maxInr (a b : ℕ) : b ⟶ max a b := ⟨Nat.le_max_right a b⟩

def maxIsCoproduct (a b : ℕ) : IsCoproduct (maxInl a b) (maxInr a b) where
  desc f g := ⟨Nat.max_le.mpr ⟨f.down, g.down⟩⟩   -- a ≤ x and b ≤ x give max a b ≤ x
  desc_inl _ _ := preorder_thin _ _
  desc_inr _ _ := preorder_thin _ _
  uniq _ _ _ _ _ := preorder_thin _ _
-- ANCHOR_END: min_max

-- ANCHOR: and_or
/-- In `Prop` ordered by implication, `p ∧ q` is a product of `p` and `q`... -/
def andFst (p q : Prop) : (p ∧ q) ⟶ p := ⟨fun h => h.1⟩
def andSnd (p q : Prop) : (p ∧ q) ⟶ q := ⟨fun h => h.2⟩

def andIsProduct (p q : Prop) : IsProduct (andFst p q) (andSnd p q) where
  lift f g := ⟨fun hx => ⟨f.down hx, g.down hx⟩⟩
  fst_lift _ _ := preorder_thin _ _
  snd_lift _ _ := preorder_thin _ _
  uniq _ _ _ _ _ := preorder_thin _ _

/-- ...and `p ∨ q` is a coproduct. -/
def orInl (p q : Prop) : p ⟶ (p ∨ q) := ⟨Or.inl⟩
def orInr (p q : Prop) : q ⟶ (p ∨ q) := ⟨Or.inr⟩

def orIsCoproduct (p q : Prop) : IsCoproduct (orInl p q) (orInr p q) where
  desc f g := ⟨fun h => h.elim f.down g.down⟩
  desc_inl _ _ := preorder_thin _ _
  desc_inr _ _ := preorder_thin _ _
  uniq _ _ _ _ _ := preorder_thin _ _
-- ANCHOR_END: and_or

/-! ## Duality -/

-- ANCHOR: duality
/-- An initial object of `C` is a terminal object of the opposite category. -/
def IsInitial.op {Obj : Type u} [Category Obj] {i : Obj} (h : IsInitial i) :
    IsTerminal (⟨i⟩ : Op Obj) where
  arrow a := h.arrow a.unop       -- a morphism `a ⟶ ⟨i⟩` in `Op` is `i ⟶ a.unop`
  unique f := h.unique f

/-- An isomorphism in the opposite category is an isomorphism in `C`, reversed. -/
def Iso.unop {Obj : Type u} [Category Obj] {a b : Obj}
    (i : (⟨a⟩ : Op Obj) ≅ ⟨b⟩) : b ≅ a where
  hom := i.hom
  inv := i.inv
  inv_hom := i.hom_inv
  hom_inv := i.inv_hom

/-- Initial objects are unique up to isomorphism: the dual of `IsTerminal.iso`,
obtained by applying it in the opposite category. No new proof is needed. -/
def IsInitial.iso {Obj : Type u} [Category Obj] {i₁ i₂ : Obj}
    (h₁ : IsInitial i₁) (h₂ : IsInitial i₂) : i₁ ≅ i₂ :=
  (IsTerminal.iso h₂.op h₁.op).unop
-- ANCHOR_END: duality

-- ANCHOR: empty_iso
/-- For example, any type that is initial is isomorphic to `Empty`. -/
def initialIsoEmpty {α : Type} (h : IsInitial α) : α ≅ Empty :=
  h.iso emptyInitial
-- ANCHOR_END: empty_iso

end Ch16
