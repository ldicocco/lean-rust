import Book.Ch16.Examples
import Book.Ch17.Functor
import Mathlib.Order.Monotone.Defs

/-!
# Chapter 17 · Functors between categories

Functors between arbitrary categories of the book's `Ch16.Category` class:
identity and composite functors, the functors on `Type` of `Functor.lean`,
monotone maps between preorders, the interpretation of a free category (a
protocol trace run as a function), a contravariant functor out of the
opposite category, and the hom functors.

This file imports `Book.Ch16.Examples`, which belongs to Chapter 16, for the
preorder, opposite and free categories.
-/

namespace Ch17

open Ch16

universe u v w

-- ANCHOR: cat_functor
/-- A functor from `C` to `D`: a map on objects and a map on morphisms that
preserves identities and composition. -/
structure CatFunctor (C : Type u) (D : Type v) [Category C] [Category D] where
  /-- The action on objects. -/
  obj : C → D
  /-- The action on morphisms: an arrow `a ⟶ b` goes to `obj a ⟶ obj b`. -/
  map : {a b : C} → (a ⟶ b) → (obj a ⟶ obj b)
  /-- Identities go to identities. -/
  map_id : ∀ (a : C), map (Category.id a) = Category.id (obj a)
  /-- Composites go to composites. -/
  map_comp : ∀ {a b c : C} (g : b ⟶ c) (f : a ⟶ b), map (g ⊚ f) = map g ⊚ map f
-- ANCHOR_END: cat_functor

namespace CatFunctor

-- ANCHOR: id_comp_functor
/-- The identity functor. -/
def id (C : Type u) [Category C] : CatFunctor C C where
  obj a := a
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The composite functor: first `F`, then `G`. -/
def comp {C : Type u} {D : Type v} {E : Type w} [Category C] [Category D] [Category E]
    (G : CatFunctor D E) (F : CatFunctor C D) : CatFunctor C E where
  obj a := G.obj (F.obj a)
  map f := G.map (F.map f)
  map_id a := by rw [F.map_id, G.map_id]
  map_comp g f := by rw [F.map_comp, G.map_comp]

/-- Composition of functors is associative and has the identity as a unit;
all three equations hold by `rfl`. -/
theorem comp_assoc {C D E B : Type} [Category C] [Category D] [Category E] [Category B]
    (H : CatFunctor E B) (G : CatFunctor D E) (F : CatFunctor C D) :
    comp H (comp G F) = comp (comp H G) F := rfl

theorem id_comp {C D : Type} [Category C] [Category D] (F : CatFunctor C D) :
    comp (id D) F = F := rfl

theorem comp_id {C D : Type} [Category C] [Category D] (F : CatFunctor C D) :
    comp F (id C) = F := rfl
-- ANCHOR_END: id_comp_functor

end CatFunctor

/-! ## Functors on types -/

-- ANCHOR: of_functor
/-- Every lawful functor on types (the class of `Functor.lean`) is a functor
from the category of types to itself. -/
def ofFunctor (F : Type → Type) [Functor F] : CatFunctor Type Type where
  obj α := F α
  map f := Functor.map f
  map_id _ := funext fun x => Functor.map_id x
  map_comp g f := funext fun x => Functor.map_comp f g x

/-- info: some 10 -/
#guard_msgs in
#eval (ofFunctor Option).map (double ⊚ len) (some "hello")
-- ANCHOR_END: of_functor

/-! ## Monotone maps -/

-- ANCHOR: monotone
/-- A monotone map between preorders is a functor between their categories.
The laws hold by `rfl`: parallel morphisms of a preorder are equal. -/
def monotoneFunctor {α β : Type} [Preorder α] [Preorder β]
    (f : α → β) (hf : Monotone f) : CatFunctor α β where
  obj := f
  map h := ⟨hf h.down⟩    -- a proof of `a ≤ b` becomes a proof of `f a ≤ f b`
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Conversely, the object map of any functor between preorders is monotone. -/
theorem CatFunctor.monotone {α β : Type} [Preorder α] [Preorder β]
    (F : CatFunctor α β) : Monotone F.obj :=
  fun _ _ h => (F.map ⟨h⟩).down

/-- Doubling is monotone on `ℕ`, hence a functor `ℕ ⥤ ℕ`. -/
def doubling : CatFunctor ℕ ℕ :=
  monotoneFunctor (fun n => 2 * n) (fun _ _ h => Nat.mul_le_mul_left 2 h)

/-- It sends the morphism `threeToFive : 3 ⟶ 5` to a morphism `6 ⟶ 10`. -/
example : doubling.map threeToFive = (⟨Nat.mul_le_mul_left 2 threeToFive.down⟩ :
    doubling.obj 3 ⟶ doubling.obj 5) := rfl

example : (doubling.obj 3, doubling.obj 5) = (6, 10) := rfl
-- ANCHOR_END: monotone

/-! ## Interpreting a free category -/

section Free

variable {V : Type} {E : V → V → Type} {D : Type u} [Category D]

-- ANCHOR: interp
/-- Interpret a path in a category `D`, given an object for every vertex and a
morphism for every edge: compose the morphisms of the edges along the path. -/
def interp (o : V → D) (m : {a b : V} → E a b → (o a ⟶ o b)) :
    {a b : V} → Path E a b → (o a ⟶ o b)
  | _, _, .nil a => Category.id (o a)
  | _, _, .cons e p => interp o m p ⊚ m e

/-- Interpreting a concatenation composes the interpretations. -/
theorem interp_append (o : V → D) (m : {a b : V} → E a b → (o a ⟶ o b))
    {a b c : V} (p : Path E a b) (q : Path E b c) :
    interp o m (p.append q) = interp o m q ⊚ interp o m p := by
  induction p with
  | nil a =>
    -- Goal: interp q = interp q ⊚ id
    exact (Category.comp_id _).symm
  | cons e p ih =>
    -- Goal: interp (append p q) ⊚ m e = interp q ⊚ (interp p ⊚ m e)
    simp only [Path.append, interp]
    rw [ih, Category.assoc]

/-- So the interpretation is a functor out of the free category. -/
def freeFunctor (o : V → D) (m : {a b : V} → E a b → (o a ⟶ o b)) :
    CatFunctor (Free E) D where
  obj v := o v.vertex
  map p := interp o m p
  map_id _ := rfl
  map_comp g f := interp_append o m f g
-- ANCHOR_END: interp

end Free

-- ANCHOR: run_protocol
/-- The data a client holds in each state of the protocol. -/
def sessionData : Conn → Type
  | .closed => Unit
  | .connected => String               -- the server
  | .authenticated => String × String  -- the server and the user

/-- What each operation does to the data. -/
def runStep : {a b : Conn} → Step a b → (sessionData a → sessionData b)
  | _, _, .connect => fun () => "db.example.org"
  | _, _, .login => fun server => (server, "alice")
  | _, _, .logout => fun (server, _) => server
  | _, _, .close => fun _ => ()

/-- Running traces is a functor from the free category to the category of types. -/
def runTrace : CatFunctor (Free Step) Type :=
  freeFunctor sessionData runStep

/-- The data after signing in, starting from the closed state. -/
def afterSignIn : String × String := runTrace.map signIn ()

/-- info: ("db.example.org", "alice") -/
#guard_msgs in
#eval afterSignIn

/-- Functoriality: running a composite trace is running its parts in turn. -/
example :
    runTrace.map (signOut ⊚ signIn) = runTrace.map signOut ⊚ runTrace.map signIn :=
  runTrace.map_comp signOut signIn
-- ANCHOR_END: run_protocol

/-! ## Contravariance and hom functors -/

-- ANCHOR: pred_functor
/-- Predicates form a functor out of the *opposite* of the category of types:
a morphism `a ⟶ b` in `Op Type` is a function `b.unop → a.unop`, and it turns
a test on `a.unop` into a test on `b.unop` by precomposition. -/
def predFunctor : CatFunctor (Op Type) Type where
  obj a := a.unop → Bool
  map f := fun p => p ∘ f
  map_id _ := rfl
  map_comp _ _ := rfl
-- ANCHOR_END: pred_functor

-- ANCHOR: hom_functor
/-- For every object `a`, the morphisms out of `a` form a functor to `Type`:
`b` goes to the type `a ⟶ b`, and `g : b ⟶ c` acts by post-composition. This
needs `a ⟶ b` to be a type, which is why the book's `Hom` lives in `Type`. -/
def homFunctor {C : Type u} [Category C] (a : C) : CatFunctor C Type where
  obj b := a ⟶ b
  map g := fun f => g ⊚ f
  map_id _ := funext fun f => Category.id_comp f
  map_comp h g := funext fun f => (Category.assoc h g f).symm

/-- In the category of types, the hom functor out of `ε` is `Reader ε`. -/
example {ε α β : Type} (g : α → β) (r : Reader ε α) :
    (homFunctor ε).map g r = Functor.map g r := rfl
-- ANCHOR_END: hom_functor

end Ch17
