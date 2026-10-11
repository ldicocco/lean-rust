import Book.Ch16.Category
import Book.Ch20.Monad
import Book.Ch20.State

/-!
# Chapter 20 · The Kleisli category

For every monad `M` (our class of `Book.Ch20.Monad`), the Kleisli category has
Lean types as objects and functions `α → M β` as morphisms. It is an instance
of the book's `Category` class of `Book.Ch16.Category`, and each category law
is proved by exactly one monad law. Conversely, the three monad laws follow
from the three category laws: the two sets of laws say the same thing.
-/

namespace Ch20

open Ch16

-- ANCHOR: kleisli_obj
/-- An object of the Kleisli category of `M`: a Lean type. The wrapper keeps
this category apart from `typeCategory`, whose objects are also types. -/
structure Kleisli (M : Type → Type) where
  /-- The underlying type. -/
  base : Type
-- ANCHOR_END: kleisli_obj

-- ANCHOR: kleisli_category
/-- The Kleisli category of a monad: a morphism from `a` to `b` is an effectful
function `a.base → M b.base`, the identity is `pure` and composition is
Kleisli composition. -/
instance kleisliCategory (M : Type → Type) [Monad M] : Category (Kleisli M) where
  Hom a b := a.base → M b.base
  id _ := Monad.pure
  comp g f := kcomp f g
  -- `id ⊚ f = f`: binding into `pure` changes nothing (right identity).
  id_comp f := kcomp_pure f
  -- `f ⊚ id = f`: binding a pure value is application (left identity).
  comp_id f := pure_kcomp f
  -- `h ⊚ (g ⊚ f) = (h ⊚ g) ⊚ f`: associativity of bind.
  assoc h g f := kcomp_assoc f g h
-- ANCHOR_END: kleisli_category

-- ANCHOR: kleisli_examples
/-- The Kleisli category of `Option`: types and partial functions. -/
abbrev Partial := Kleisli Option

def text : Partial := ⟨String⟩
def qty : Partial := ⟨Nat⟩

/-- Two partial functions, as morphisms. -/
def parseM : text ⟶ qty := parseQty
def checkM : qty ⟶ qty := checkQty

/-- Their composite, written with the category's `⊚`: first parse, then check. -/
def readQtyM : text ⟶ qty := checkM ⊚ parseM

/-- info: [some 12, none, none] -/
#guard_msgs in
#eval ["12", "twelve", "500"].map readQtyM

/-- The Kleisli category of `List`: types and nondeterministic functions,
which are relations. -/
def item : Kleisli List := ⟨String⟩
def site : Kleisli List := ⟨String⟩

def stockedAt : item ⟶ site := warehouses
def collectedBy : site ⟶ site := carriers

/-- info: ["DHL", "UPS", "Geodis"] -/
#guard_msgs in
#eval (collectedBy ⊚ stockedAt) "bolts"
-- ANCHOR_END: kleisli_examples

-- ANCHOR: monad_ops
/-- The operations of a monad without the laws. -/
structure MonadOps (M : Type → Type) where
  pure : {α : Type} → α → M α
  bind : {α β : Type} → M α → (α → M β) → M β

/-- Kleisli composition, defined from the raw operations. -/
def MonadOps.kcomp {M : Type → Type} (ops : MonadOps M) {α β γ : Type}
    (f : α → M β) (g : β → M γ) : α → M γ :=
  fun a => ops.bind (f a) g

/-- The monad laws, stated with `bind`. -/
def MonadOps.BindLaws {M : Type → Type} (ops : MonadOps M) : Prop :=
  (∀ {α β : Type} (a : α) (f : α → M β), ops.bind (ops.pure a) f = f a) ∧
  (∀ {α : Type} (m : M α), ops.bind m ops.pure = m) ∧
  (∀ {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ),
    ops.bind (ops.bind m f) g = ops.bind m (fun a => ops.bind (f a) g))

/-- The category laws of the Kleisli category, stated with `kcomp`. -/
def MonadOps.KleisliLaws {M : Type → Type} (ops : MonadOps M) : Prop :=
  (∀ {α β : Type} (f : α → M β), ops.kcomp ops.pure f = f) ∧
  (∀ {α β : Type} (f : α → M β), ops.kcomp f ops.pure = f) ∧
  (∀ {α β γ δ : Type} (f : α → M β) (g : β → M γ) (h : γ → M δ),
    ops.kcomp (ops.kcomp f g) h = ops.kcomp f (ops.kcomp g h))
-- ANCHOR_END: monad_ops

-- ANCHOR: laws_iff
/-- The monad laws hold if and only if Kleisli composition satisfies the laws of
a category. -/
theorem bindLaws_iff_kleisliLaws {M : Type → Type} (ops : MonadOps M) :
    ops.BindLaws ↔ ops.KleisliLaws := by
  constructor
  · -- From bind laws to category laws: apply each law pointwise.
    intro ⟨pure_bind, bind_pure, bind_assoc⟩
    refine ⟨?_, ?_, ?_⟩
    · intro α β f
      funext a
      exact pure_bind a f
    · intro α β f
      funext a
      exact bind_pure (f a)
    · intro α β γ δ f g h
      funext a
      exact bind_assoc (f a) g h
  · -- From category laws to bind laws: a computation `m : M α` is the
    -- Kleisli arrow `fun () => m` applied to `()`.
    intro ⟨pure_kcomp, kcomp_pure, kcomp_assoc⟩
    refine ⟨?_, ?_, ?_⟩
    · intro α β a f
      exact congrFun (pure_kcomp f) a
    · intro α m
      exact congrFun (kcomp_pure (fun (_ : Unit) => m)) ()
    · intro α β γ m f g
      exact congrFun (kcomp_assoc (fun (_ : Unit) => m) f g) ()
-- ANCHOR_END: laws_iff

end Ch20
