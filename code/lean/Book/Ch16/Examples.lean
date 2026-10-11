import Book.Ch16.Category
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

/-!
# Chapter 16 · Examples of categories

Many small categories built with the book's `Category` class: types and
functions (with a commutative square), preorders (`ℕ` with `≤`, `Prop` with
implication), monoids as one-object categories, discrete categories, and the
free category of paths in a graph (the traces of a connection protocol). Then
isomorphisms, monomorphisms and epimorphisms, with proofs.
-/

namespace Ch16

universe u

open Category

/-! ## Types and functions -/

-- ANCHOR: type_examples
/-- In `typeCategory`, a morphism `String ⟶ ℕ` is just a function. -/
def len : String ⟶ ℕ := String.length

def double : ℕ ⟶ ℕ := fun n => 2 * n

def isEven : ℕ ⟶ Bool := fun n => n % 2 == 0

/-- info: 10 -/
#guard_msgs in
#eval (double ⊚ len) "hello"

/-- info: true -/
#guard_msgs in
#eval (isEven ⊚ double ⊚ len) "abc"
-- ANCHOR_END: type_examples

-- ANCHOR: type_laws
/-- The laws hold by `rfl`: both sides are the same function, up to unfolding. -/
example : (isEven ⊚ double) ⊚ len = isEven ⊚ (double ⊚ len) := rfl
example : double ⊚ Category.id ℕ = double := rfl
-- ANCHOR_END: type_laws

-- ANCHOR: square
/-- Concatenate the two lists of a pair. -/
def appendPair : List ℕ × List ℕ ⟶ List ℕ := fun p => p.1 ++ p.2
/-- Measure both lists of a pair. -/
def lengths : List ℕ × List ℕ ⟶ ℕ × ℕ := fun p => (p.1.length, p.2.length)
/-- Add the two numbers of a pair. -/
def addPair : ℕ × ℕ ⟶ ℕ := fun p => p.1 + p.2

/-- The square commutes: "append, then measure" equals "measure both, then add". -/
theorem length_square :
    (List.length : List ℕ ⟶ ℕ) ⊚ appendPair = addPair ⊚ lengths := by
  funext p                  -- two functions are equal if they agree on every `p`
  exact List.length_append  -- (p.1 ++ p.2).length = p.1.length + p.2.length
-- ANCHOR_END: square

/-! ## Preorders -/

-- ANCHOR: preorder
/-- Every preorder is a category with at most one morphism between two objects:
a morphism `a ⟶ b` is a proof of `a ≤ b`, wrapped by `PLift` so that it lives
in `Type`. -/
instance preorderCategory (α : Type) [Preorder α] : Category α where
  Hom a b := PLift (a ≤ b)
  id a := ⟨le_refl a⟩
  comp g f := ⟨le_trans f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
-- ANCHOR_END: preorder

-- ANCHOR: preorder_examples
/-- The morphism `3 ⟶ 5` in the category `ℕ`: a proof that `3 ≤ 5`. -/
def threeToFive : (3 : ℕ) ⟶ 5 := ⟨by decide⟩

/-- Any two parallel morphisms of a preorder are equal: proofs are irrelevant. -/
theorem preorder_thin {α : Type} [Preorder α] {a b : α} (f g : a ⟶ b) : f = g := by
  cases f   -- `f` is `⟨h₁⟩` for some proof `h₁ : a ≤ b`
  cases g   -- `g` is `⟨h₂⟩` for some proof `h₂ : a ≤ b`
  rfl       -- `h₁` and `h₂` are proofs of the same proposition, hence equal

/-- In `Prop`, ordered by implication, a morphism `p ⟶ q` is a proof of `p → q`. -/
def andElim (p q : Prop) : (p ∧ q) ⟶ p := ⟨fun h => h.1⟩
-- ANCHOR_END: preorder_examples

/-! ## Monoids -/

-- ANCHOR: one_object
/-- The single object of the category built from a monoid `M`. -/
structure OneObject (M : Type) where
  /-- The unique value: the type has exactly one element, `⟨⟩`. -/
  mk ::

/-- A monoid is a category with one object: the morphisms are the elements of
the monoid, composition is multiplication, the identity is `1`. -/
instance monoidCategory (M : Type) [Monoid M] : Category (OneObject M) where
  Hom _ _ := M
  id _ := 1
  comp g f := g * f
  id_comp f := one_mul f
  comp_id f := mul_one f
  assoc h g f := (mul_assoc h g f).symm
-- ANCHOR_END: one_object

-- ANCHOR: one_object_eval
/-- An element of the monoid, seen as a morphism of its one-object category. -/
def OneObject.arrow {M : Type} [Monoid M] (m : M) : (⟨⟩ : OneObject M) ⟶ ⟨⟩ := m

/-- In the one-object category of `(ℕ, *, 1)`, composing is multiplying. -/
def six : (⟨⟩ : OneObject ℕ) ⟶ ⟨⟩ := OneObject.arrow 2 ⊚ OneObject.arrow 3

/-- info: 6 -/
#guard_msgs in
#eval (six : ℕ)
-- ANCHOR_END: one_object_eval

-- ANCHOR: endo_monoid
/-- Conversely, in any category the morphisms from an object to itself form a
monoid under composition: the monoid laws are instances of the category laws. -/
theorem endo_monoid {Obj : Type u} [Category Obj] (a : Obj) (f g h : a ⟶ a) :
    Category.id a ⊚ f = f ∧ f ⊚ Category.id a = f ∧ h ⊚ (g ⊚ f) = (h ⊚ g) ⊚ f :=
  ⟨Category.id_comp f, Category.comp_id f, Category.assoc h g f⟩
-- ANCHOR_END: endo_monoid

/-! ## Discrete categories -/

-- ANCHOR: discrete
/-- A copy of `α` whose only morphisms are identities. -/
structure Discrete (α : Type) where
  /-- The underlying element. -/
  val : α

/-- A morphism `a ⟶ b` is a proof that `a = b`. -/
instance discreteCategory (α : Type) : Category (Discrete α) where
  Hom a b := PLift (a = b)
  id _ := ⟨rfl⟩
  comp g f := ⟨f.down.trans g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Between two different objects there is no morphism at all. -/
theorem discrete_no_arrow (f : (⟨1⟩ : Discrete ℕ) ⟶ ⟨2⟩) : False := by
  have h : (⟨1⟩ : Discrete ℕ) = ⟨2⟩ := f.down
  simp at h
-- ANCHOR_END: discrete

/-! ## Free categories: paths in a graph -/

-- ANCHOR: path
/-- A path in a graph whose edges from `a` to `b` form the type `E a b`:
either empty, or an edge followed by a path. -/
inductive Path {V : Type} (E : V → V → Type) : V → V → Type where
  | nil (a : V) : Path E a a
  | cons {a b c : V} (e : E a b) (p : Path E b c) : Path E a c

namespace Path

variable {V : Type} {E : V → V → Type}

/-- Concatenation: first `p`, then `q`. -/
def append : {a b c : V} → Path E a b → Path E b c → Path E a c
  | _, _, _, nil _, q => q
  | _, _, _, cons e p, q => cons e (append p q)

/-- The number of edges in a path. -/
def length : {a b : V} → Path E a b → ℕ
  | _, _, nil _ => 0
  | _, _, cons _ p => length p + 1
-- ANCHOR_END: path

-- ANCHOR: path_laws
/-- The empty path is a left unit: true by the first equation of `append`. -/
theorem nil_append {a b : V} (p : Path E a b) : append (nil a) p = p := rfl

/-- The empty path is a right unit: needs induction on the path. -/
theorem append_nil {a b : V} (p : Path E a b) : append p (nil b) = p := by
  induction p with
  | nil a => rfl
  | cons e p ih =>
    -- Goal: append (cons e p) (nil _) = cons e p
    simp only [append]  -- unfold one step: cons e (append p (nil _)) = cons e p
    rw [ih]             -- the induction hypothesis closes it

/-- Concatenation is associative, again by induction on the first path. -/
theorem append_assoc {a b c d : V} (p : Path E a b) (q : Path E b c) (r : Path E c d) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | nil a => rfl
  | cons e p ih => simp only [append, ih]
-- ANCHOR_END: path_laws

end Path

-- ANCHOR: free_category
/-- The objects of the free category on a graph `E` are its vertices. -/
structure Free {V : Type} (E : V → V → Type) where
  /-- The vertex. -/
  vertex : V

/-- The free category: morphisms are paths, composition is concatenation. -/
instance freeCategory {V : Type} (E : V → V → Type) : Category (Free E) where
  Hom a b := Path E a.vertex b.vertex
  id a := Path.nil a.vertex
  comp g f := Path.append f g
  id_comp f := Path.append_nil f
  comp_id f := Path.nil_append f
  assoc h g f := Path.append_assoc f g h
-- ANCHOR_END: free_category

-- ANCHOR: protocol
/-- The states of a network connection. -/
inductive Conn where
  | closed | connected | authenticated

/-- The protocol: which operation leads from which state to which. -/
inductive Step : Conn → Conn → Type where
  | connect : Step .closed .connected
  | login : Step .connected .authenticated
  | logout : Step .authenticated .connected
  | close : Step .connected .closed

/-- The name of an operation, for printing. -/
def Step.name : {a b : Conn} → Step a b → String
  | _, _, .connect => "connect"
  | _, _, .login => "login"
  | _, _, .logout => "logout"
  | _, _, .close => "close"

/-- The operations along a path, in order. -/
def Path.names : {a b : Conn} → Path Step a b → List String
  | _, _, .nil _ => []
  | _, _, .cons e p => e.name :: p.names

/-- Morphisms of the free category on the protocol graph are valid traces. -/
abbrev Trace (a b : Conn) : Type := (⟨a⟩ : Free Step) ⟶ ⟨b⟩

def signIn : Trace .closed .authenticated :=
  .cons .connect (.cons .login (.nil _))

def signOut : Trace .authenticated .closed :=
  .cons .logout (.cons .close (.nil _))

/-- info: ["connect", "login", "logout", "close"] -/
#guard_msgs in
#eval (signOut ⊚ signIn).names
-- ANCHOR_END: protocol

/-! ## Isomorphisms -/

-- ANCHOR: iso_examples
/-- `Bool` and `Option Unit` are isomorphic in the category of types. -/
def boolIso : Bool ≅ Option Unit where
  hom := fun b => if b then some () else none
  inv := fun o => o.isSome
  inv_hom := by
    funext b      -- compare the two functions on every `b : Bool`
    cases b <;> rfl
  hom_inv := by
    funext o
    cases o <;> rfl

/-- Swapping the components of a pair is an isomorphism `α × β ≅ β × α`. -/
def swapIso (α β : Type) : α × β ≅ β × α where
  hom := fun p => (p.2, p.1)
  inv := fun p => (p.2, p.1)
  inv_hom := rfl
  hom_inv := rfl
-- ANCHOR_END: iso_examples

-- ANCHOR: inverse_unique
/-- A morphism has at most one inverse: if `g` is a left inverse and `g'` a
right inverse of `f`, then `g = g'`. -/
theorem inverse_unique {Obj : Type u} [Category Obj] {a b : Obj}
    (f : a ⟶ b) (g g' : b ⟶ a)
    (hg : g ⊚ f = Category.id a) (hg' : f ⊚ g' = Category.id b) : g = g' :=
  calc g = g ⊚ Category.id b := (Category.comp_id g).symm
    _ = g ⊚ (f ⊚ g') := by rw [hg']
    _ = (g ⊚ f) ⊚ g' := Category.assoc g f g'
    _ = Category.id a ⊚ g' := by rw [hg]
    _ = g' := Category.id_comp g'
-- ANCHOR_END: inverse_unique

/-! ## Monomorphisms and epimorphisms -/

-- ANCHOR: mono_epi
/-- `f` is a monomorphism if it can be cancelled on the left. -/
def Mono {Obj : Type u} [Category Obj] {a b : Obj} (f : a ⟶ b) : Prop :=
  ∀ {x : Obj} (g h : x ⟶ a), f ⊚ g = f ⊚ h → g = h

/-- `f` is an epimorphism if it can be cancelled on the right. -/
def Epi {Obj : Type u} [Category Obj] {a b : Obj} (f : a ⟶ b) : Prop :=
  ∀ {y : Obj} (g h : b ⟶ y), g ⊚ f = h ⊚ f → g = h
-- ANCHOR_END: mono_epi

-- ANCHOR: mono_injective
/-- In the category of types, the monomorphisms are the injective functions. -/
theorem mono_iff_injective {α β : Type} (f : α ⟶ β) :
    Mono f ↔ Function.Injective f := by
  constructor
  · -- A mono is injective: test it with two functions out of `Unit`.
    intro hf x y hxy
    have h := hf (fun _ : Unit => x) (fun _ : Unit => y) (funext fun _ => hxy)
    exact congrFun h ()
  · -- An injective function can be cancelled: compare `g` and `h` pointwise.
    intro hf x g h hgh
    funext t
    exact hf (congrFun hgh t)
-- ANCHOR_END: mono_injective

-- ANCHOR: epi_surjective
/-- In the category of types, the epimorphisms are the surjective functions. -/
theorem epi_iff_surjective {α β : Type} (f : α ⟶ β) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · -- An epi is surjective: test it with two predicates on `β`.
    intro hf b
    let g : β ⟶ Prop := fun y => ∃ a, f a = y
    let h : β ⟶ Prop := fun _ => True
    have hgf : g ⊚ f = h ⊚ f := by
      funext a
      exact eq_true ⟨a, rfl⟩  -- `∃ a', f a' = f a` holds, so it equals `True`
    have hgh : g = h := hf g h hgf
    exact of_eq_true (congrFun hgh b)
  · -- A surjective function can be cancelled: every `b` is some `f a`.
    intro hf y g h hgh
    funext b
    obtain ⟨a, rfl⟩ := hf b
    exact congrFun hgh a
-- ANCHOR_END: epi_surjective

-- ANCHOR: mono_epi_not_iso
/-- In a preorder every morphism is both mono and epi (parallel morphisms are
equal), but `0 ⟶ 1` in `ℕ` is not an isomorphism: that would need `1 ≤ 0`. -/
def zeroToOne : (0 : ℕ) ⟶ 1 := ⟨by decide⟩

theorem zeroToOne_mono : Mono zeroToOne :=
  fun g h _ => preorder_thin g h

theorem zeroToOne_epi : Epi zeroToOne :=
  fun g h _ => preorder_thin g h

theorem zero_one_not_iso (i : (0 : ℕ) ≅ 1) : False := by
  have h : 1 ≤ 0 := i.inv.down
  omega
-- ANCHOR_END: mono_epi_not_iso

end Ch16
