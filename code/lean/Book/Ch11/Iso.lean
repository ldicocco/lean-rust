import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Nat.Notation

/-!
# Chapter 11 · Isomorphisms of types

Our own `Iso` structure (two functions that undo each other), the laws of the
algebra of types proved as isomorphisms (units, commutativity, associativity,
distributivity, currying, the laws of exponents), congruence lemmas that let us
chain isomorphisms like equations, and the connection with Mathlib's `Equiv`.
-/

namespace Ch11

-- ANCHOR: iso
/-- An isomorphism between `α` and `β`: a function in each direction, and proofs
that each one undoes the other. -/
structure Iso (α β : Type) where
  /-- The forward function. -/
  toFun : α → β
  /-- The backward function. -/
  invFun : β → α
  /-- Going forward and then back is the identity on `α`. -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- Going back and then forward is the identity on `β`. -/
  right_inv : ∀ b, toFun (invFun b) = b

/-- `α ≅ β` is the type of isomorphisms between `α` and `β`. -/
scoped infix:25 " ≅ " => Iso
-- ANCHOR_END: iso

namespace Iso

variable {α β γ α' β' : Type}

-- ANCHOR: equivalence
/-- Every type is isomorphic to itself. -/
def refl (α : Type) : α ≅ α where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl

/-- An isomorphism can be run backwards. -/
def symm (i : α ≅ β) : β ≅ α where
  toFun := i.invFun
  invFun := i.toFun
  left_inv := i.right_inv
  right_inv := i.left_inv

/-- Isomorphisms compose. -/
def trans (i : α ≅ β) (j : β ≅ γ) : α ≅ γ where
  toFun a := j.toFun (i.toFun a)
  invFun c := i.invFun (j.invFun c)
  left_inv a := by
    -- Goal: i.invFun (j.invFun (j.toFun (i.toFun a))) = a
    rw [j.left_inv, i.left_inv]
  right_inv c := by
    -- Goal: j.toFun (i.toFun (i.invFun (j.invFun c))) = c
    rw [i.right_inv, j.right_inv]
-- ANCHOR_END: equivalence

/-! ## The laws of the algebra of types -/

-- ANCHOR: prod_unit
/-- `α × 1 ≅ α`: pairing with the unit value adds no information. -/
def prodUnit (α : Type) : α × Unit ≅ α where
  toFun p := p.1
  invFun a := (a, ())
  left_inv := by
    intro ⟨a, u⟩  -- take the pair apart
    cases u       -- the only value of `Unit` is `()`
    rfl           -- goal: (a, ()) = (a, ()), true by computation
  right_inv _ := rfl
-- ANCHOR_END: prod_unit

-- ANCHOR: prod_comm_assoc
/-- `α × β ≅ β × α`. -/
def prodComm (α β : Type) : α × β ≅ β × α where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `(α × β) × γ ≅ α × (β × γ)`. -/
def prodAssoc (α β γ : Type) : (α × β) × γ ≅ α × (β × γ) where
  toFun p := (p.1.1, (p.1.2, p.2))
  invFun p := ((p.1, p.2.1), p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
-- ANCHOR_END: prod_comm_assoc

-- ANCHOR: sum_laws
/-- `α + β ≅ β + α`. -/
def sumComm (α β : Type) : α ⊕ β ≅ β ⊕ α where
  toFun
    | .inl a => .inr a
    | .inr b => .inl b
  invFun
    | .inl b => .inr b
    | .inr a => .inl a
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

/-- `α + 0 ≅ α`: a summand with no values contributes nothing. -/
def sumEmpty (α : Type) : α ⊕ Empty ≅ α where
  toFun
    | .inl a => a
    | .inr e => nomatch e
  invFun a := .inl a
  left_inv s := by
    cases s with
    | inl a => rfl
    | inr e => nomatch e  -- no value of `Empty`: nothing to prove
  right_inv _ := rfl

/-- `α × 0 ≅ 0`: a pair needs a component of type `Empty`, which does not exist. -/
def prodEmpty (α : Type) : α × Empty ≅ Empty where
  toFun p := nomatch p.2
  invFun e := nomatch e
  left_inv p := nomatch p.2
  right_inv e := nomatch e
-- ANCHOR_END: sum_laws

-- ANCHOR: distrib
/-- `α × (β + γ) ≅ α × β + α × γ`: distributivity. -/
def distrib (α β γ : Type) : α × (β ⊕ γ) ≅ (α × β) ⊕ (α × γ) where
  toFun
    | (a, .inl b) => .inl (a, b)
    | (a, .inr c) => .inr (a, c)
  invFun
    | .inl (a, b) => (a, .inl b)
    | .inr (a, c) => (a, .inr c)
  left_inv := by
    intro ⟨a, s⟩
    cases s <;> rfl
  right_inv := by
    intro s
    cases s <;> rfl
-- ANCHOR_END: distrib

-- ANCHOR: exponentials
/-- `γ ^ (α × β) ≅ (γ ^ β) ^ α`: currying. -/
def curry (α β γ : Type) : (α × β → γ) ≅ (α → β → γ) where
  toFun f a b := f (a, b)
  invFun g p := g p.1 p.2
  left_inv f := by
    funext p  -- two functions are equal if they agree on every argument
    rfl       -- goal: f (p.1, p.2) = f p, true because p = (p.1, p.2)
  right_inv _ := rfl

/-- `α ^ (β + γ) ≅ α ^ β × α ^ γ`: a function out of a sum is a pair of
functions, one per summand. -/
def sumArrow (α β γ : Type) : (β ⊕ γ → α) ≅ (β → α) × (γ → α) where
  toFun f := (fun b => f (.inl b), fun c => f (.inr c))
  invFun p
    | .inl b => p.1 b
    | .inr c => p.2 c
  left_inv f := by
    funext s
    cases s <;> rfl
  right_inv _ := rfl

/-- `α ^ 1 ≅ α`: a function out of `Unit` is just one value. -/
def unitArrow (α : Type) : (Unit → α) ≅ α where
  toFun f := f ()
  invFun a := fun _ => a
  left_inv f := by
    funext u
    cases u
    rfl
  right_inv _ := rfl

/-- `1 ^ α ≅ 1`: there is exactly one function into `Unit`. -/
def arrowUnit (α : Type) : (α → Unit) ≅ Unit where
  toFun _ := ()
  invFun _ := fun _ => ()
  left_inv _ := rfl
  right_inv _ := rfl

/-- `α ^ 0 ≅ 1`: there is exactly one function out of `Empty`. -/
def emptyArrow (α : Type) : (Empty → α) ≅ Unit where
  toFun _ := ()
  invFun _ := fun e => nomatch e
  left_inv f := by
    funext e
    nomatch e
  right_inv _ := rfl
-- ANCHOR_END: exponentials

-- ANCHOR: option_bool
/-- `Option α ≅ 1 + α`. -/
def optionSum (α : Type) : Option α ≅ Unit ⊕ α where
  toFun
    | none => .inl ()
    | some a => .inr a
  invFun
    | .inl () => none
    | .inr a => some a
  left_inv o := by cases o <;> rfl
  right_inv s := by
    cases s with
    | inl u => cases u; rfl
    | inr a => rfl

/-- `Bool ≅ 1 + 1`: a boolean is a choice between two empty messages. -/
def boolSum : Bool ≅ Unit ⊕ Unit where
  toFun b := if b then .inl () else .inr ()
  invFun
    | .inl () => true
    | .inr () => false
  left_inv b := by cases b <;> rfl
  right_inv s := by
    cases s with
    | inl u => cases u; rfl
    | inr u => cases u; rfl
-- ANCHOR_END: option_bool

/-! ## Congruence: replacing a type by an isomorphic one -/

-- ANCHOR: congr
/-- Isomorphic components give isomorphic products. -/
def prodCongr (i : α ≅ α') (j : β ≅ β') : α × β ≅ α' × β' where
  toFun p := (i.toFun p.1, j.toFun p.2)
  invFun p := (i.invFun p.1, j.invFun p.2)
  left_inv p := by simp only [i.left_inv, j.left_inv]
  right_inv p := by simp only [i.right_inv, j.right_inv]

/-- Isomorphic domains and codomains give isomorphic function types. -/
def arrowCongr (i : α ≅ α') (j : β ≅ β') : (α → β) ≅ (α' → β') where
  toFun f := fun a' => j.toFun (f (i.invFun a'))
  invFun g := fun a => j.invFun (g (i.toFun a))
  left_inv f := by
    funext a
    simp only [i.left_inv, j.left_inv]
  right_inv g := by
    funext a'
    simp only [i.right_inv, j.right_inv]
-- ANCHOR_END: congr

/-! ## Putting it together: `α ^ 2 ≅ α × α`, by algebra -/

-- ANCHOR: square
/-- `(Bool → α) ≅ α × α`, derived step by step like the equation
`α ^ 2 = α ^ (1 + 1) = α ^ 1 × α ^ 1 = α × α`. -/
def boolArrow (α : Type) : (Bool → α) ≅ α × α :=
  (arrowCongr boolSum (refl α))                       -- α ^ 2       ≅ α ^ (1 + 1)
    |>.trans (sumArrow α Unit Unit)                   --             ≅ α ^ 1 × α ^ 1
    |>.trans (prodCongr (unitArrow α) (unitArrow α))  --             ≅ α × α
-- ANCHOR_END: square

-- ANCHOR: square_eval
/-- info: (10, 20) -/
#guard_msgs in
#eval (boolArrow ℕ).toFun (fun b => if b then 10 else 20)

/-- info: [7, 8] -/
#guard_msgs in
#eval [true, false].map ((boolArrow ℕ).invFun (7, 8))
-- ANCHOR_END: square_eval

/-! ## In Mathlib: `Equiv` -/

-- ANCHOR: to_equiv
/-- Our `Iso` is Mathlib's `Equiv`, field for field. -/
def toEquiv (i : α ≅ β) : α ≃ β where
  toFun := i.toFun
  invFun := i.invFun
  left_inv := i.left_inv
  right_inv := i.right_inv

/-- And back. -/
def ofEquiv (e : α ≃ β) : α ≅ β where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
-- ANCHOR_END: to_equiv

end Iso

-- ANCHOR: mathlib_equiv
/-- info: Equiv.prodSumDistrib ℕ Bool String : ℕ × (Bool ⊕ String) ≃ ℕ × Bool ⊕ ℕ × String -/
#guard_msgs in
#check Equiv.prodSumDistrib ℕ Bool String

/-- info: Equiv.curry ℕ Bool String : (ℕ × Bool → String) ≃ (ℕ → Bool → String) -/
#guard_msgs in
#check Equiv.curry ℕ Bool String

/-- info: Sum.inr (3, "hi") -/
#guard_msgs in
#eval Equiv.prodSumDistrib ℕ Bool String (3, .inr "hi")

/-- An `Equiv` is applied like a function; `e.symm` is its inverse. -/
example : (Equiv.prodSumDistrib ℕ Bool String).symm (.inl (3, true)) = (3, .inl true) :=
  rfl

/-- Library isomorphisms combine with `Equiv.prodCongr`, `Equiv.trans` and so on. -/
example (α : Type) : α × (Bool ⊕ Empty) ≃ α × Bool :=
  Equiv.prodCongr (Equiv.refl α) (Equiv.sumEmpty Bool Empty)
-- ANCHOR_END: mathlib_equiv

end Ch11
