import Mathlib.Data.List.Dedup

/-!
# Chapter 18 · Parametricity, one function at a time

Reynolds' relational reading of the type `List α → List α`, proved for
`List.reverse` and specialized to a function graph to recover naturality; a
family with a `DecidableEq` constraint that is not natural; and the reason the
general free theorem cannot be proved inside Lean: with classical choice, Lean
defines a "polymorphic identity" that is not the identity.
-/

namespace Ch18.Param

-- ANCHOR: list_rel
/-- The relational lifting of `R` to lists: two lists are related when they
have the same length and related elements in every position. -/
inductive ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a b xs ys} : R a b → ListRel R xs ys → ListRel R (a :: xs) (b :: ys)
-- ANCHOR_END: list_rel

-- ANCHOR: list_rel_append
/-- Related lists concatenate to related lists. -/
theorem ListRel.append {α β : Type} {R : α → β → Prop} {xs ys xs' ys'}
    (h : ListRel R xs ys) (h' : ListRel R xs' ys') :
    ListRel R (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => exact h'
  | cons hab _ ih => exact ListRel.cons hab ih
-- ANCHOR_END: list_rel_append

-- ANCHOR: reverse_param
/-- **Parametricity of `reverse`.** For every relation `R` between any two
types, `reverse` sends related lists to related lists. -/
theorem reverse_param {α β : Type} (R : α → β → Prop) {xs : List α} {ys : List β}
    (h : ListRel R xs ys) : ListRel R xs.reverse ys.reverse := by
  induction h with
  | nil => exact ListRel.nil
  | cons hab _ ih =>
    -- reverse (a :: xs) = reverse xs ++ [a], and the same on the right.
    simp only [List.reverse_cons]
    exact ih.append (ListRel.cons hab ListRel.nil)
-- ANCHOR_END: reverse_param

-- ANCHOR: graph
/-- When `R` is the graph of a function `f`, related lists are exactly a list
and its image under `map f`. -/
theorem listRel_graph {α β : Type} (f : α → β) (xs : List α) (ys : List β) :
    ListRel (fun a b => f a = b) xs ys ↔ xs.map f = ys := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons hab _ ih => simp [hab, ih]
  · intro h
    subst h
    induction xs with
    | nil => exact ListRel.nil
    | cons a rest ih => exact ListRel.cons rfl ih
-- ANCHOR_END: graph

-- ANCHOR: free_theorem_reverse
/-- The free theorem for `reverse`, obtained from parametricity by choosing the
graph of `f` as the relation: naturality. -/
theorem reverse_natural {α β : Type} (f : α → β) (xs : List α) :
    xs.reverse.map f = (xs.map f).reverse := by
  have related : ListRel (fun a b => f a = b) xs (xs.map f) :=
    (listRel_graph f xs (xs.map f)).mpr rfl
  exact (listRel_graph f _ _).mp (reverse_param _ related)
-- ANCHOR_END: free_theorem_reverse

-- ANCHOR: dedup
/-- `dedup` needs `DecidableEq`: it compares elements. It commutes with `map f`
for injective `f` (Mathlib proves this as `List.dedup_map_of_injective`)... -/
example (f : ℕ → ℕ) (hf : Function.Injective f) (xs : List ℕ) :
    (xs.map f).dedup = xs.dedup.map f :=
  List.dedup_map_of_injective hf xs

/-- ...but not for a map that identifies two elements. -/
example : ([1, 2].map fun _ => (0 : ℕ)).dedup ≠ ([1, 2] : List ℕ).dedup.map fun _ => 0 := by
  decide
-- ANCHOR_END: dedup

-- ANCHOR: free_theorem_id
/-- The free theorem for `∀ α, α → α`, stated *inside* Lean as a proposition
about every function of that type. -/
def FreeTheoremId : Prop :=
  ∀ (f : (α : Type) → α → α) (α : Type) (a : α), f α a = a
-- ANCHOR_END: free_theorem_id

-- ANCHOR: not_id
open Classical in
/-- A "polymorphic identity" that inspects its type argument. Classical logic
lets it ask whether `α` is `Bool` (a question no program could decide), and on
`Bool` it negates. -/
noncomputable def notId (α : Type) (a : α) : α :=
  if h : α = Bool then cast h.symm (!(cast h a)) else a

theorem notId_true : notId Bool true = false := by
  simp [notId]

/-- So the internal free theorem is not just unprovable: in Lean (with its
standard axioms) it is false. -/
theorem not_freeTheoremId : ¬ FreeTheoremId := by
  intro h
  have : notId Bool true = true := h notId Bool true
  rw [notId_true] at this
  exact Bool.false_ne_true this
-- ANCHOR_END: not_id

-- ANCHOR: not_id_axioms
/-- info: 'Ch18.Param.not_freeTheoremId' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_freeTheoremId

/-- info: 'Ch18.Param.reverse_natural' depends on axioms: [propext] -/
#guard_msgs in
#print axioms reverse_natural
-- ANCHOR_END: not_id_axioms

end Ch18.Param
