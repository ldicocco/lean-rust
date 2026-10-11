import Mathlib.Data.Nat.Notation

/-!
# Chapter 17 · Functors on types

Kinds (`Type → Type` is an ordinary function type), a `Functor` class with the
functor laws as fields, lawful instances for `Option`, `List`, a binary tree,
`Except ε`, pairs and functions; a "functor" that breaks the laws; core Lean's
`Functor` and `LawfulFunctor`; contravariant functors, bifunctors and
profunctors; and map fusion, proved once for every lawful functor.
-/

namespace Ch17

/-! ## Kinds -/

-- ANCHOR: kinds
/-- info: Option.{u} (α : Type u) : Type u -/
#guard_msgs in
#check Option

/-- info: Option ℕ : Type -/
#guard_msgs in
#check Option ℕ

/-- A type constructor of kind `Type → Type → Type`, partially applied. -/
example : Type → Type := Except String

/-- Type-level functions can be written with `fun`, like any other function. -/
def Twice : Type → Type := fun α => α × α

/-- info: (1, 2) -/
#guard_msgs in
#eval ((1, 2) : Twice ℕ)
-- ANCHOR_END: kinds

-- ANCHOR: reader
/-- Functions out of a fixed type `ε`: the kind is `Type → Type` once `ε` is
fixed. A named definition makes this partial application possible. -/
def Reader (ε α : Type) : Type := ε → α
-- ANCHOR_END: reader

/-! ## The `Functor` class -/

-- ANCHOR: functor_class
/-- A functor on types: a type constructor `F` with a `map` that satisfies the
two functor laws. (This class shadows core Lean's `Functor` inside `Ch17`;
core's is `_root_.Functor`.) -/
class Functor (F : Type → Type) where
  /-- Apply a function to every value of type `α` inside an `F α`. -/
  map : {α β : Type} → (α → β) → F α → F β
  /-- Mapping the identity changes nothing. -/
  map_id : ∀ {α : Type} (x : F α), map id x = x
  /-- Mapping a composite is mapping one function, then the other. -/
  map_comp : ∀ {α β γ : Type} (f : α → β) (g : β → γ) (x : F α),
    map (g ∘ f) x = map g (map f x)
-- ANCHOR_END: functor_class

-- ANCHOR: option_functor
instance : Functor Option where
  map f
    | none => none
    | some a => some (f a)
  map_id x := by
    cases x <;> rfl          -- check `none` and `some a` separately
  map_comp f g x := by
    cases x <;> rfl
-- ANCHOR_END: option_functor

-- ANCHOR: list_functor
/-- `map` on lists, written out (it is `List.map`). -/
def listMap {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | a :: as => f a :: listMap f as

theorem listMap_id {α : Type} (xs : List α) : listMap id xs = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    -- Goal: listMap id (a :: as) = a :: as
    simp only [listMap, id, ih]

theorem listMap_comp {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
    listMap (g ∘ f) xs = listMap g (listMap f xs) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    -- Goal: (g ∘ f) a :: listMap (g ∘ f) as = g (f a) :: listMap g (listMap f as)
    simp only [listMap, Function.comp, ih]

instance : Functor List where
  map := listMap
  map_id := listMap_id
  map_comp := listMap_comp
-- ANCHOR_END: list_functor

-- ANCHOR: tree
/-- Binary trees with values at the nodes. -/
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
  deriving Repr

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | .leaf => .leaf
  | .node l a r => .node (l.map f) (f a) (r.map f)

theorem Tree.map_id {α : Type} (t : Tree α) : t.map id = t := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
    -- Goal: (node l a r).map id = node l a r; one induction hypothesis per subtree
    simp only [Tree.map, id, ihl, ihr]

theorem Tree.map_comp {α β γ : Type} (f : α → β) (g : β → γ) (t : Tree α) :
    t.map (g ∘ f) = (t.map f).map g := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr => simp only [Tree.map, Function.comp, ihl, ihr]

instance : Functor Tree where
  map := Tree.map
  map_id := Tree.map_id
  map_comp := Tree.map_comp
-- ANCHOR_END: tree

-- ANCHOR: tree_eval
def sample : Tree ℕ := .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)

/--
info: Ch17.Tree.node
  (Ch17.Tree.node (Ch17.Tree.leaf) "1" (Ch17.Tree.leaf))
  "2"
  (Ch17.Tree.node (Ch17.Tree.leaf) "3" (Ch17.Tree.leaf))
-/
#guard_msgs in
#eval Functor.map toString sample
-- ANCHOR_END: tree_eval

-- ANCHOR: more_functors
/-- `Except ε` maps the success value and leaves errors alone, like Rust's
`Result::map`. -/
instance (ε : Type) : Functor (Except ε) where
  map f
    | .error e => .error e
    | .ok a => .ok (f a)
  map_id x := by cases x <;> rfl
  map_comp f g x := by cases x <;> rfl

/-- `Prod ε` (pairs `ε × α`) maps the second component, like a Rust tuple
`(E, A)` with a label of type `E` attached to the value. -/
instance (ε : Type) : Functor (Prod ε) where
  map f p := (p.1, f p.2)
  map_id _ := rfl
  map_comp _ _ _ := rfl

/-- `Reader ε` maps the result: `map f r` is "first `r`, then `f`". -/
instance (ε : Type) : Functor (Reader ε) where
  map f r := fun e => f (r e)
  map_id _ := rfl
  map_comp _ _ _ := rfl
-- ANCHOR_END: more_functors

/-! ## Laws that fail -/

-- ANCHOR: bad_functors
/-- A `map` for `Option` that forgets everything. It satisfies the composition
law but not the identity law. -/
def forgetMap {α β : Type} (_ : α → β) (_ : Option α) : Option β := none

theorem forgetMap_comp {α β γ : Type} (f : α → β) (g : β → γ) (x : Option α) :
    forgetMap (g ∘ f) x = forgetMap g (forgetMap f x) := rfl

theorem forgetMap_not_id : ¬ ∀ x : Option ℕ, forgetMap id x = x := by
  intro h
  have h1 := h (some 1)   -- forgetMap id (some 1) = some 1, that is, none = some 1
  simp [forgetMap] at h1

/-- A `map` on pairs that counts how often it is called (like a Rust `map`
that also increments a counter). It breaks both laws. -/
def countingMap {α β : Type} (f : α → β) (p : ℕ × α) : ℕ × β := (p.1 + 1, f p.2)

theorem countingMap_not_id : countingMap id (0, "a") ≠ (0, "a") := by
  simp [countingMap]
-- ANCHOR_END: bad_functors

/-! ## Generic theorems -/

-- ANCHOR: map_fusion
/-- Map fusion, for every lawful functor: mapping twice is mapping once with the
composite. A compiler (or an iterator adapter) may rewrite one into the other. -/
theorem map_map {F : Type → Type} [Functor F] {α β γ : Type}
    (f : α → β) (g : β → γ) (x : F α) :
    Functor.map g (Functor.map f x) = Functor.map (fun a => g (f a)) x :=
  (Functor.map_comp f g x).symm
-- ANCHOR_END: map_fusion

-- ANCHOR: pipeline
/-- A pipeline of transformations of numbers, applied in order. -/
def Pipeline := List (ℕ → ℕ)

/-- Run the pipeline "naively": one `map` per stage. -/
def runNaive {F : Type → Type} [Functor F] : Pipeline → F ℕ → F ℕ
  | [], x => x
  | f :: fs, x => runNaive fs (Functor.map f x)

/-- Compose all the stages into a single function. -/
def fuse : Pipeline → (ℕ → ℕ)
  | [] => id
  | f :: fs => fuse fs ∘ f

/-- Fusion is correct for every lawful functor: one `map` of the fused function
gives the same result as one `map` per stage. -/
theorem runNaive_eq_fuse {F : Type → Type} [Functor F] (p : Pipeline) (x : F ℕ) :
    runNaive p x = Functor.map (fuse p) x := by
  induction p generalizing x with
  | nil =>
    -- Goal: x = map id x. This is the identity law, read right to left.
    exact (Functor.map_id x).symm
  | cons f fs ih =>
    -- Goal: runNaive fs (map f x) = map (fuse fs ∘ f) x
    simp only [runNaive, fuse]
    rw [ih, Functor.map_comp]  -- both sides become map (fuse fs) (map f x)
-- ANCHOR_END: pipeline

-- ANCHOR: pipeline_eval
def stages : Pipeline := [(· + 1), (· * 10), (· - 3)]

/-- info: some 17 -/
#guard_msgs in
#eval Functor.map (fuse stages) (some 1)

/-- info: [17, 27, 37] -/
#guard_msgs in
#eval runNaive stages [1, 2, 3]
-- ANCHOR_END: pipeline_eval

/-! ## Core Lean's `Functor` and `LawfulFunctor` -/

-- ANCHOR: core_functor
/-- Core Lean's class has only the operation; `<$>` is its notation. -/
instance : _root_.Functor Tree where
  map := Tree.map

/-- The laws live in a separate class, `LawfulFunctor`. -/
instance : LawfulFunctor Tree where
  map_const := rfl                           -- `mapConst` has its default definition
  id_map t := Tree.map_id t
  comp_map f g t := Tree.map_comp f g t

/-- info: Ch17.Tree.node (Ch17.Tree.leaf) 20 (Ch17.Tree.leaf) -/
#guard_msgs in
#eval (· * 10) <$> Tree.node .leaf 2 .leaf

/-- Lemmas proved once for all lawful functors now apply to `Tree`. -/
example (t : Tree ℕ) : (· + 1) <$> (· * 2) <$> t = (fun n => n * 2 + 1) <$> t := by
  simp only [Functor.map_map]
-- ANCHOR_END: core_functor

/-! ## Contravariant functors -/

-- ANCHOR: contravariant
/-- A contravariant functor: `contramap` turns `α → β` into `F β → F α`, and the
composition law reverses the order. -/
class Contravariant (F : Type → Type) where
  contramap : {α β : Type} → (α → β) → F β → F α
  contramap_id : ∀ {α : Type} (x : F α), contramap id x = x
  contramap_comp : ∀ {α β γ : Type} (f : α → β) (g : β → γ) (x : F γ),
    contramap (g ∘ f) x = contramap f (contramap g x)

/-- A predicate on `α`: a test that every value passes or fails. -/
def Pred (α : Type) : Type := α → Bool

/-- To test a `β` given a test on `γ`, convert first: precomposition. -/
instance : Contravariant Pred where
  contramap f p := fun a => p (f a)
  contramap_id _ := rfl
  contramap_comp _ _ _ := rfl

/-- A comparator, like the closures passed to Rust's `sort_by`. -/
def Comparator (α : Type) : Type := α → α → Ordering

/-- Compare values by comparing a key computed from them (`sort_by_key`). -/
instance : Contravariant Comparator where
  contramap f c := fun a b => c (f a) (f b)
  contramap_id _ := rfl
  contramap_comp _ _ _ := rfl
-- ANCHOR_END: contravariant

-- ANCHOR: contravariant_eval
def isLong : Pred ℕ := fun n => n > 3

/-- "Is the string long?" is "is its length long?". -/
def isLongString : Pred String := Contravariant.contramap String.length isLong

/-- info: [false, true] -/
#guard_msgs in
#eval ["abc", "abcd"].map isLongString
-- ANCHOR_END: contravariant_eval

/-! ## Bifunctors and profunctors -/

-- ANCHOR: bifunctor
/-- A bifunctor maps both of its arguments, covariantly. -/
class Bifunctor (F : Type → Type → Type) where
  bimap : {α β γ δ : Type} → (α → γ) → (β → δ) → F α β → F γ δ
  bimap_id : ∀ {α β : Type} (x : F α β), bimap id id x = x
  bimap_comp : ∀ {α β γ δ ε ζ : Type} (f : α → γ) (f' : γ → ε) (g : β → δ) (g' : δ → ζ)
    (x : F α β), bimap (f' ∘ f) (g' ∘ g) x = bimap f' g' (bimap f g x)

instance : Bifunctor Prod where
  bimap f g p := (f p.1, g p.2)
  bimap_id _ := rfl
  bimap_comp _ _ _ _ _ := rfl

/-- `Except ε α` maps the error with the first function and the value with the
second: Rust's `map_err` and `map` together. -/
instance : Bifunctor Except where
  bimap f g
    | .error e => .error (f e)
    | .ok a => .ok (g a)
  bimap_id x := by cases x <;> rfl
  bimap_comp _ _ _ _ x := by cases x <;> rfl
-- ANCHOR_END: bifunctor

-- ANCHOR: profunctor
/-- Functions are contravariant in the input and covariant in the output:
`dimap f g h` is "first `f`, then `h`, then `g`". -/
def dimap {α β γ δ : Type} (f : γ → α) (g : β → δ) (h : α → β) : γ → δ :=
  g ∘ h ∘ f

theorem dimap_id {α β : Type} (h : α → β) : dimap id id h = h := rfl

theorem dimap_comp {α β γ δ ε ζ : Type} (f : γ → α) (f' : ε → γ)
    (g : β → δ) (g' : δ → ζ) (h : α → β) :
    dimap (f ∘ f') (g' ∘ g) h = dimap f' g' (dimap f g h) := rfl
-- ANCHOR_END: profunctor

end Ch17
