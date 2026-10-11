/-!
# Chapter 5 · Constructive and classical reasoning in Lean

What Lean proves without axioms (double-negation introduction, the collapse of
triple negation, the double negation of excluded middle, the De Morgan laws
that hold constructively), what needs `Classical` (double-negation
elimination, Peirce's law, the remaining De Morgan law, the drinker), how
`#print axioms` tells them apart, why the classical principles stand or fall
together, `Decidable` and why `if` on a `Prop` needs it, and the
double-negation "monad" inside which classical reasoning is constructive.
-/

namespace Ch05

/-! ## Constructive proofs -/

-- ANCHOR: constructive
/-- Double-negation introduction: a proof of `p` refutes every refutation. -/
theorem dni (p : Prop) : p → ¬¬p :=
  fun hp hnp => hnp hp

/-- Triple negation collapses to single negation. -/
theorem tne (p : Prop) : ¬¬¬p → ¬p :=
  fun hnnnp hp => hnnnp (dni p hp)

/-- Contraposition, in the direction that holds. -/
theorem contra (p q : Prop) : (p → q) → (¬q → ¬p) :=
  fun hpq hnq hp => hnq (hpq hp)

/-- Two De Morgan laws hold in both directions or in one. -/
theorem not_or_iff (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
   fun ⟨hnp, hnq⟩ h => h.elim hnp hnq⟩

theorem not_and_of_or_not (p q : Prop) : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h ⟨hp, hq⟩ => h.elim (fun hnp => hnp hp) (fun hnq => hnq hq)
-- ANCHOR_END: constructive

-- ANCHOR: nn_em
/-- Excluded middle cannot be refuted. The refutation `k` is called twice. -/
theorem nn_em (p : Prop) : ¬¬(p ∨ ¬p) := by
  intro k              -- k : ¬(p ∨ ¬p); goal: False
  apply k              -- goal: p ∨ ¬p
  right                -- commit to the right disjunct; goal: ¬p
  intro hp             -- hp : p; goal: False
  apply k              -- use k a second time; goal: p ∨ ¬p
  left                 -- now we can commit to the left disjunct
  exact hp
-- ANCHOR_END: nn_em

-- ANCHOR: nn_em_term
/--
info: theorem Ch05.nn_em : ∀ (p : Prop), ¬¬(p ∨ ¬p) :=
fun p k => k (Or.inr fun hp => k (Or.inl hp))
-/
#guard_msgs in
#print nn_em
-- ANCHOR_END: nn_em_term

/-! ## Classical proofs -/

-- ANCHOR: classical_axioms
/-- info: Classical.em (p : Prop) : p ∨ ¬p -/
#guard_msgs in
#check Classical.em

/-- info: Classical.byContradiction {p : Prop} (h : ¬p → False) : p -/
#guard_msgs in
#check Classical.byContradiction

/-- info: axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α -/
#guard_msgs in
#print Classical.choice
-- ANCHOR_END: classical_axioms

-- ANCHOR: classical
/-- Double-negation elimination: proof by contradiction. -/
theorem dne (p : Prop) : ¬¬p → p := by
  intro hnnp
  apply Classical.byContradiction   -- goal: ¬p → False
  intro hnp
  exact hnnp hnp

/-- Peirce's law, by cases on excluded middle. -/
theorem peirce (p q : Prop) : ((p → q) → p) → p := by
  intro h
  cases Classical.em p with
  | inl hp => exact hp
  | inr hnp => exact h (fun hp => absurd hp hnp)

/-- The De Morgan law that fails constructively. `by_cases` splits on
`Classical.em`. -/
theorem not_and_or (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  by_cases hp : p
  · right
    intro hq
    exact h ⟨hp, hq⟩
  · left
    exact hp
-- ANCHOR_END: classical

-- ANCHOR: print_axioms
/-- info: 'Ch05.nn_em' does not depend on any axioms -/
#guard_msgs in
#print axioms nn_em

/-- info: 'Ch05.not_or_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms not_or_iff

/-- info: 'Ch05.dne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dne

/-- info: 'Ch05.not_and_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_and_or
-- ANCHOR_END: print_axioms

/-! ## All or nothing -/

-- ANCHOR: all_or_nothing
/-- If excluded middle holds for every proposition, so does double-negation
elimination... -/
theorem dne_of_em (em : ∀ p : Prop, p ∨ ¬p) : ∀ p : Prop, ¬¬p → p := by
  intro p hnnp
  cases em p with
  | inl hp => exact hp
  | inr hnp => exact absurd hnp hnnp

/-- ...and conversely: apply double-negation elimination to `nn_em`. -/
theorem em_of_dne (dne : ∀ p : Prop, ¬¬p → p) : ∀ p : Prop, p ∨ ¬p :=
  fun p => dne (p ∨ ¬p) (nn_em p)

/-- Peirce's law implies excluded middle: take `q := False` and the
proposition `p ∨ ¬p`. -/
theorem em_of_peirce (peirce : ∀ p q : Prop, ((p → q) → p) → p) :
    ∀ p : Prop, p ∨ ¬p := by
  intro p
  apply peirce (p ∨ ¬p) False   -- goal: (p ∨ ¬p → False) → p ∨ ¬p
  intro k                       -- k : ¬(p ∨ ¬p)
  exact (nn_em p k).elim

/-- info: 'Ch05.em_of_peirce' does not depend on any axioms -/
#guard_msgs in
#print axioms em_of_peirce
-- ANCHOR_END: all_or_nothing

/-! ## Double negation as a monad: Glivenko -/

-- ANCHOR: nn_monad
/-- `pure` for double negation: the same term as `dni`. -/
theorem nn_pure {p : Prop} (hp : p) : ¬¬p :=
  fun k => k hp

/-- `bind` for double negation: to refute a refutation of `q`, run the
double-negated `p` with a continuation that feeds each `p` to `f`. -/
theorem nn_bind {p q : Prop} (nnp : ¬¬p) (f : p → ¬¬q) : ¬¬q :=
  fun k => nnp (fun hp => f hp k)

/-- Inside `¬¬`, excluded middle is available, so the classical De Morgan law
holds there, with no axioms. -/
theorem nn_not_and_or (p q : Prop) : ¬¬(¬(p ∧ q) → ¬p ∨ ¬q) := by
  apply nn_bind (nn_em p)   -- borrow `p ∨ ¬p` inside the double negation
  intro hem
  apply nn_pure             -- now prove the formula itself
  intro h
  cases hem with
  | inl hp => exact Or.inr (fun hq => h ⟨hp, hq⟩)
  | inr hnp => exact Or.inl hnp

/-- info: 'Ch05.nn_not_and_or' does not depend on any axioms -/
#guard_msgs in
#print axioms nn_not_and_or
-- ANCHOR_END: nn_monad

-- ANCHOR: nn_more
/-- The double negations of the other classical laws are constructive too. -/
theorem nn_dne (p : Prop) : ¬¬(¬¬p → p) :=
  nn_bind (nn_em p) fun hem =>
    nn_pure fun hnnp => hem.elim id (fun hnp => absurd hnp hnnp)

theorem nn_peirce (p q : Prop) : ¬¬(((p → q) → p) → p) :=
  nn_bind (nn_em p) fun hem =>
    nn_pure fun h => hem.elim id (fun hnp => h (fun hp => absurd hp hnp))
-- ANCHOR_END: nn_more

/-! ## Existence without a witness -/

-- ANCHOR: witness
/-- A constructive existence proof contains its witness. -/
theorem exists_square : ∃ n : Nat, n * n = 49 := ⟨7, rfl⟩

/-- The drinker: in a nonempty pub there is someone such that, if they drink,
everyone drinks. The proof asks whether everyone drinks, a question it cannot
answer by computation, and so it never says who the person is. -/
theorem drinker {α : Type} [Inhabited α] (drinks : α → Prop) :
    ∃ x, drinks x → ∀ y, drinks y := by
  by_cases h : ∀ y, drinks y
  · exact ⟨default, fun _ => h⟩       -- anyone will do
  · obtain ⟨y, hy⟩ := Classical.not_forall.mp h   -- someone does not drink
    exact ⟨y, fun hdy => absurd hdy hy⟩

/-- info: 'Ch05.exists_square' does not depend on any axioms -/
#guard_msgs in
#print axioms exists_square

/-- info: 'Ch05.drinker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms drinker
-- ANCHOR_END: witness

/-! ## Decidable propositions -/

-- ANCHOR: decidable_print
/--
info: inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
-/
#guard_msgs in
#print Decidable
-- ANCHOR_END: decidable_print

-- ANCHOR: if_prop
/-- `if` on a proposition needs a `Decidable` instance: a procedure that
says which side holds. For `n % 2 = 0` on `Nat`, Lean has one. -/
def parity (n : Nat) : String :=
  if n % 2 = 0 then "even" else "odd"

/-- info: "odd" -/
#guard_msgs in
#eval parity 7

-- With an arbitrary `p`, there is no procedure, and Lean says so.
/--
error: failed to synthesize instance of type class
  Decidable p

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def choose (p : Prop) : Nat := if p then 1 else 0

/-- Asking for the instance as an argument moves the obligation to the caller. -/
def choose' (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- info: 1 -/
#guard_msgs in
#eval choose' (3 < 5)
-- ANCHOR_END: if_prop

-- ANCHOR: noncomputable
/-- `Classical.propDecidable` makes every proposition "decidable" by the
axiom of choice, but the result cannot be run: there is no code behind it. -/
noncomputable def chooseClassical (p : Prop) : Nat :=
  have := Classical.propDecidable p
  if p then 1 else 0
-- ANCHOR_END: noncomputable

end Ch05
