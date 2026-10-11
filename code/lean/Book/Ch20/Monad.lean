/-!
# Chapter 20 · A monad class with laws

Our own `Monad` class, built from scratch: a type constructor with `pure` and
`bind`, and the three monad laws as fields. Instances for `Option`, `Except`
and `List`, with the laws proved. Derived operations (`map`, `join`, Kleisli
composition) and the theorems that connect them: the functor laws, the laws of
`join`, and the monad laws restated as laws of Kleisli composition. Finally,
every lawful monad of Lean's core library is an instance of our class.

Inside `namespace Ch20` the name `Monad` refers to the class below. Lean's own
class is `_root_.Monad`.
-/

namespace Ch20

-- ANCHOR: monad_class
/-- A monad: a type constructor `M` with two operations and three laws. -/
class Monad (M : Type → Type) where
  /-- Wrap a plain value in a computation that has no effect. -/
  pure : {α : Type} → α → M α
  /-- Run `m`, then feed its result to `f`. -/
  bind : {α β : Type} → M α → (α → M β) → M β
  /-- Left identity: binding a pure value is just function application. -/
  pure_bind : ∀ {α β : Type} (a : α) (f : α → M β), bind (pure a) f = f a
  /-- Right identity: binding into `pure` changes nothing. -/
  bind_pure : ∀ {α : Type} (m : M α), bind m pure = m
  /-- Associativity: only the order of the steps matters, not their nesting. -/
  bind_assoc : ∀ {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ),
    bind (bind m f) g = bind m (fun a => bind (f a) g)
-- ANCHOR_END: monad_class

-- ANCHOR: option_monad
/-- `Option` is the monad of computations that may fail without a reason. -/
instance optionMonad : Monad Option where
  pure a := some a
  bind m f :=
    match m with
    | none => none
    | some a => f a
  pure_bind _ _ := rfl
  bind_pure m := by
    cases m <;> rfl
  bind_assoc m _ _ := by
    cases m <;> rfl
-- ANCHOR_END: option_monad

-- ANCHOR: except_monad
/-- `Except ε` is the monad of computations that may fail with an error of
type `ε`: Lean's `Result`. -/
instance exceptMonad (ε : Type) : Monad (Except ε) where
  pure a := .ok a
  bind m f :=
    match m with
    | .error e => .error e
    | .ok a => f a
  pure_bind _ _ := rfl
  bind_pure m := by
    cases m <;> rfl
  bind_assoc m _ _ := by
    cases m <;> rfl
-- ANCHOR_END: except_monad

-- ANCHOR: list_bind
/-- `bind` for lists: apply `f` to every element and concatenate the results.
(This is `List.flatMap`, Rust's `flat_map`; we write it out to prove things
about it.) -/
def listBind {α β : Type} : List α → (α → List β) → List β
  | [], _ => []
  | a :: as, f => f a ++ listBind as f

/-- `listBind` distributes over `++`. -/
theorem listBind_append {α β : Type} (xs ys : List α) (f : α → List β) :
    listBind (xs ++ ys) f = listBind xs f ++ listBind ys f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    -- Goal: listBind (x :: xs ++ ys) f = listBind (x :: xs) f ++ listBind ys f
    simp only [List.cons_append, listBind, ih, List.append_assoc]
-- ANCHOR_END: list_bind

-- ANCHOR: list_monad
/-- `List` is the monad of nondeterministic computations: a computation returns
every possible result. -/
instance listMonad : Monad List where
  pure a := [a]
  bind := listBind
  pure_bind a f := by
    -- listBind [a] f = f a ++ [] = f a
    simp [listBind]
  bind_pure m := by
    induction m with
    | nil => rfl
    | cons a as ih => simp [listBind, ih]
  bind_assoc m f g := by
    induction m with
    | nil => rfl
    | cons a as ih => simp [listBind, listBind_append, ih]
-- ANCHOR_END: list_monad

-- ANCHOR: examples
/-- A quantity parsed from text: fails on anything that is not a number. -/
def parseQty (s : String) : Option Nat := s.toNat?

/-- A quantity is accepted only between 1 and 100. -/
def checkQty (n : Nat) : Option Nat := if 1 ≤ n ∧ n ≤ 100 then some n else none

/-- info: (some 12, none, none) -/
#guard_msgs in
#eval (Monad.bind (parseQty "12") checkQty,
       Monad.bind (parseQty "twelve") checkQty,
       Monad.bind (parseQty "500") checkQty)

/-- Every warehouse that has `item`, nondeterministically. -/
def warehouses : String → List String
  | "bolts" => ["Hamburg", "Lyon"]
  | "nuts" => ["Lyon"]
  | _ => []

/-- Every carrier that collects from a warehouse. -/
def carriers : String → List String
  | "Hamburg" => ["DHL", "UPS"]
  | "Lyon" => ["Geodis"]
  | _ => []

/-- info: ["DHL", "UPS", "Geodis"] -/
#guard_msgs in
#eval Monad.bind (warehouses "bolts") carriers
-- ANCHOR_END: examples

section Derived

variable {M : Type → Type} [Monad M] {α β γ δ : Type}

-- ANCHOR: derived
/-- Every monad is a functor: `map f m` runs `m` and applies `f` to the result. -/
def map (f : α → β) (m : M α) : M β :=
  Monad.bind m (fun a => Monad.pure (f a))

/-- Flatten a computation that returns a computation. -/
def join (mm : M (M α)) : M α :=
  Monad.bind mm (fun m => m)

/-- Kleisli composition: first `f`, then `g`, effects included. (Haskell and
Lean's own library write it `f >=> g`.) -/
def kcomp (f : α → M β) (g : β → M γ) : α → M γ :=
  fun a => Monad.bind (f a) g
-- ANCHOR_END: derived

-- ANCHOR: functor_laws
/-- The functor laws of Chapter 17 follow from the monad laws. -/
theorem map_id (m : M α) : map (fun a => a) m = m :=
  Monad.bind_pure m

theorem map_comp (f : α → β) (g : β → γ) (m : M α) :
    map (fun a => g (f a)) m = map g (map f m) := by
  -- Unfold `map`; the right side is a bind of a bind.
  simp only [map]
  -- Reassociate, then the inner `bind (pure (f a)) _` is a left identity.
  rw [Monad.bind_assoc]
  simp only [Monad.pure_bind]
-- ANCHOR_END: functor_laws

-- ANCHOR: join_laws
/-- `bind` is `map` followed by `join`: the categorical definition of a monad
uses `pure`, `map` and `join` instead of `pure` and `bind`. -/
theorem bind_eq_join_map (m : M α) (f : α → M β) :
    Monad.bind m f = join (map f m) := by
  -- Right side: bind (bind m (fun a => pure (f a))) (fun m => m)
  simp only [join, map]
  -- Reassociate: bind m (fun a => bind (pure (f a)) (fun m => m))
  rw [Monad.bind_assoc]
  -- Left identity turns the inner bind into f a.
  simp only [Monad.pure_bind]

/-- Unit laws for `join`: wrapping with `pure` outside or inside, then
flattening, gives back what we started with. -/
theorem join_pure (m : M α) : join (Monad.pure m) = m :=
  Monad.pure_bind m (fun m => m)

theorem join_map_pure (m : M α) : join (map Monad.pure m) = m := by
  rw [← bind_eq_join_map, Monad.bind_pure]

/-- Associativity of `join`: a three-layer computation can be flattened from
the outside or from the inside. -/
theorem join_join (mmm : M (M (M α))) : join (join mmm) = join (map join mmm) := by
  simp only [join, map]
  -- Reassociate the outer bind on each side.
  rw [Monad.bind_assoc, Monad.bind_assoc]
  -- On the right, `bind (pure (join mm)) id` is `join mm` by left identity.
  simp only [Monad.pure_bind]
-- ANCHOR_END: join_laws

-- ANCHOR: kleisli_laws
/-- The three monad laws, restated for Kleisli composition: `pure` is a left
and a right identity, and `kcomp` is associative. -/
theorem pure_kcomp (f : α → M β) : kcomp Monad.pure f = f := by
  funext a
  exact Monad.pure_bind a f

theorem kcomp_pure (f : α → M β) : kcomp f Monad.pure = f := by
  funext a
  exact Monad.bind_pure (f a)

theorem kcomp_assoc (f : α → M β) (g : β → M γ) (h : γ → M δ) :
    kcomp (kcomp f g) h = kcomp f (kcomp g h) := by
  funext a
  exact Monad.bind_assoc (f a) g h
-- ANCHOR_END: kleisli_laws

end Derived

-- ANCHOR: of_lawful
/-- Every monad of Lean's library that comes with a `LawfulMonad` instance
gives an instance of our class: the laws are already proved there. -/
abbrev Monad.ofLawful (M : Type → Type) [_root_.Monad M] [LawfulMonad M] : Monad M where
  pure := Pure.pure
  bind := Bind.bind
  pure_bind := LawfulMonad.pure_bind
  bind_pure := _root_.bind_pure
  bind_assoc := LawfulMonad.bind_assoc
-- ANCHOR_END: of_lawful

end Ch20
