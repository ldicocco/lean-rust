import Mathlib.Data.Nat.Notation

/-!
# Chapter 18 · Natural transformations between functors on types

A functor class with laws (Chapter 17's, redefined here so that this chapter
does not depend on Chapter 17's files), the functors `Option`, `List`, the
identity and the constant functors, natural transformations between them,
naturality proved for `List.head?`, `Option.toList`, `List.reverse`,
`List.length` and `some`, and vertical composition of natural transformations.
-/

namespace Ch18

-- ANCHOR: type_functor
/-- A functor from the category of Lean types to itself: a type constructor `F`
with a `map` that preserves identities and composition. -/
class TypeFunctor (F : Type → Type) where
  map : {α β : Type} → (α → β) → F α → F β
  map_id : ∀ {α : Type} (x : F α), map id x = x
  map_comp : ∀ {α β γ : Type} (g : β → γ) (f : α → β) (x : F α),
    map (g ∘ f) x = map g (map f x)
-- ANCHOR_END: type_functor

open TypeFunctor

-- ANCHOR: instances
instance : TypeFunctor Option where
  map := Option.map
  map_id x := by cases x <;> rfl
  map_comp _ _ x := by cases x <;> rfl

instance : TypeFunctor List where
  map := List.map
  map_id x := List.map_id x
  map_comp _ _ _ := List.map_map.symm

/-- The identity functor: `Ident α` is just `α`. -/
def Ident (α : Type) : Type := α

instance : TypeFunctor Ident where
  map f x := f x
  map_id _ := rfl
  map_comp _ _ _ := rfl

/-- The constant functor: `Const C α` is `C`, whatever `α` is, and `map f`
does nothing. -/
def Const (C : Type) (_ : Type) : Type := C

instance (C : Type) : TypeFunctor (Const C) where
  map _ x := x
  map_id _ := rfl
  map_comp _ _ _ := rfl
-- ANCHOR_END: instances

-- ANCHOR: nat_trans
/-- A natural transformation from `F` to `G`: one function `F α → G α` for
every type `α` (the *components*), such that every naturality square
commutes. -/
structure NatTrans (F G : Type → Type) [TypeFunctor F] [TypeFunctor G] where
  app : (α : Type) → F α → G α
  naturality : ∀ {α β : Type} (f : α → β) (x : F α),
    app β (map f x) = map f (app α x)
-- ANCHOR_END: nat_trans

-- ANCHOR: head_nat
/-- `List.head?` is natural: taking the head and then mapping is the same as
mapping and then taking the head. -/
def headNat : NatTrans List Option where
  app _ := List.head?
  naturality f xs := by
    -- Goal: (List.map f xs).head? = Option.map f xs.head?
    cases xs with
    | nil => rfl            -- both sides are `none`
    | cons a rest => rfl    -- both sides are `some (f a)`
-- ANCHOR_END: head_nat

-- ANCHOR: to_list_nat
/-- `Option.toList` is natural (Rust's `Option::into_iter`, collected). -/
def toListNat : NatTrans Option List where
  app _ := Option.toList
  naturality f o := by
    cases o <;> rfl
-- ANCHOR_END: to_list_nat

-- ANCHOR: reverse_nat
/-- `List.reverse` is natural. This time the two paths agree only after an
induction on the list. -/
theorem map_reverse' {α β : Type} (f : α → β) (xs : List α) :
    List.map f xs.reverse = (List.map f xs).reverse := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    -- Goal: map f (reverse (a :: rest)) = reverse (map f (a :: rest))
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, ih]

def reverseNat : NatTrans List List where
  app _ := List.reverse
  naturality f xs := (map_reverse' f xs).symm
-- ANCHOR_END: reverse_nat

-- ANCHOR: more_nats
/-- `List.length` is a natural transformation into a constant functor:
mapping does not change the length. -/
def lengthNat : NatTrans List (Const ℕ) where
  app _ := List.length
  naturality f xs := List.length_map (as := xs) f

/-- `some` is a natural transformation from the identity functor to `Option`. -/
def someNat : NatTrans Ident Option where
  app _ x := some x
  naturality _ _ := rfl
-- ANCHOR_END: more_nats

-- ANCHOR: eval_nats
/-- info: some 3 -/
#guard_msgs in
#eval headNat.app ℕ [3, 1, 2]

/-- info: [2, 1, 3] -/
#guard_msgs in
#eval reverseNat.app ℕ [3, 1, 2]
-- ANCHOR_END: eval_nats

-- ANCHOR: vcomp
/-- Vertical composition: first `η : F ⇒ G`, then `θ : G ⇒ H`. -/
def NatTrans.vcomp {F G H : Type → Type} [TypeFunctor F] [TypeFunctor G]
    [TypeFunctor H] (θ : NatTrans G H) (η : NatTrans F G) : NatTrans F H where
  app α x := θ.app α (η.app α x)
  naturality f x := by
    -- Goal: θ.app β (η.app β (map f x)) = map f (θ.app α (η.app α x))
    rw [η.naturality, θ.naturality]

/-- The identity natural transformation. -/
def NatTrans.id (F : Type → Type) [TypeFunctor F] : NatTrans F F where
  app _ x := x
  naturality _ _ := rfl
-- ANCHOR_END: vcomp

-- ANCHOR: first_as_list
/-- "The first element, as a list of length at most one": natural with no new
proof, because it is a composite of natural transformations. -/
def firstAsList : NatTrans List List := toListNat.vcomp headNat

/-- info: [3] -/
#guard_msgs in
#eval firstAsList.app ℕ [3, 1, 2]

example (f : ℕ → String) (xs : List ℕ) :
    firstAsList.app String (xs.map f) = (firstAsList.app ℕ xs).map f :=
  firstAsList.naturality f xs
-- ANCHOR_END: first_as_list

-- ANCHOR: ext
/-- Two natural transformations are equal when their components are. The
naturality fields are proofs, and any two proofs of the same proposition are
equal, so they take care of themselves. -/
theorem NatTrans.ext' {F G : Type → Type} [TypeFunctor F] [TypeFunctor G]
    {η θ : NatTrans F G} (h : ∀ α x, η.app α x = θ.app α x) : η = θ := by
  cases η with
  | mk app₁ nat₁ =>
    cases θ with
    | mk app₂ nat₂ =>
      -- Turn the pointwise equality into an equality of functions.
      have : app₁ = app₂ := funext fun α => funext fun x => h α x
      subst this
      rfl
-- ANCHOR_END: ext

-- ANCHOR: vcomp_laws
variable {F G H K : Type → Type} [TypeFunctor F] [TypeFunctor G] [TypeFunctor H]
  [TypeFunctor K]

theorem NatTrans.id_vcomp (η : NatTrans F G) : (NatTrans.id G).vcomp η = η :=
  NatTrans.ext' fun _ _ => rfl

theorem NatTrans.vcomp_id (η : NatTrans F G) : η.vcomp (NatTrans.id F) = η :=
  NatTrans.ext' fun _ _ => rfl

theorem NatTrans.vcomp_assoc (ι : NatTrans H K) (θ : NatTrans G H)
    (η : NatTrans F G) : ι.vcomp (θ.vcomp η) = (ι.vcomp θ).vcomp η :=
  NatTrans.ext' fun _ _ => rfl
-- ANCHOR_END: vcomp_laws

-- ANCHOR: latest_nat
/-- The last `n` elements of a list (Rust's `latest` in `ch18_log_tail.rs`). -/
def latest {α : Type} (n : ℕ) (xs : List α) : List α := xs.drop (xs.length - n)

/-- `latest n` is natural, so `map f` can be moved after it. -/
def latestNat (n : ℕ) : NatTrans List List where
  app _ := latest n
  naturality f xs := by
    -- Unfold `latest` and the list functor's `map`:
    show (xs.map f).drop ((xs.map f).length - n) = (xs.drop (xs.length - n)).map f
    -- `map` does not change the length, and it commutes with `drop`.
    rw [List.length_map, List.map_drop]

/-- info: ["#8", "#9", "#10"] -/
#guard_msgs in
#eval (latestNat 3).app String ((List.range' 1 10).map fun i => s!"#{i}")
-- ANCHOR_END: latest_nat

end Ch18
