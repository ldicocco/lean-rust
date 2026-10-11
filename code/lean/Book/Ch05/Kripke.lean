import Mathlib.Order.Defs.PartialOrder
import Book.Ch04.Deep

/-!
# Chapter 5 · Kripke semantics

Kripke models (a preorder of worlds with a monotone valuation), the forcing
relation, the monotonicity lemma, and soundness of the natural-deduction
system of Chapter 4 (imported from `Book.Ch04.Deep`) with respect to every
Kripke model. A two-world model refutes excluded middle, double-negation
elimination and Peirce's law, checked by `decide`; a three-world fork refutes
one De Morgan law and weak excluded middle. By soundness, none of these
formulas is derivable, although all of them are tautologies.
-/

namespace Ch05

open Ch04

-- ANCHOR: model
/-- A Kripke model over a preordered set of worlds `W`. Read `w ≤ w'` as
"`w'` is a possible future of `w`, where we know at least as much", and
`val w n` as "at world `w`, atom `n` is known to hold". Knowledge is never
lost: that is `mono`. -/
structure KripkeModel (W : Type) [Preorder W] where
  val : W → Nat → Bool
  mono : ∀ {w w' : W} {n : Nat}, w ≤ w' → val w n = true → val w' n = true
-- ANCHOR_END: model

variable {W : Type} [Preorder W]

-- ANCHOR: forces
/-- The forcing relation `w ⊩ A`. Only implication looks at other worlds: it
must hold in every future, not just now. -/
def Forces (M : KripkeModel W) : W → Formula → Prop
  | w, .var n   => M.val w n = true
  | _, .top     => True
  | _, .bot     => False
  | w, .and A B => Forces M w A ∧ Forces M w B
  | w, .or A B  => Forces M w A ∨ Forces M w B
  | w, .imp A B => ∀ w', w ≤ w' → Forces M w' A → Forces M w' B
-- ANCHOR_END: forces

-- ANCHOR: forces_neg
/-- Unfolding the definition for negation: `w ⊩ ¬A` means that no future of
`w` forces `A`. -/
theorem forces_neg (M : KripkeModel W) (w : W) (A : Formula) :
    Forces M w A.neg ↔ ∀ w', w ≤ w' → ¬ Forces M w' A := by
  simp [Formula.neg, Forces]
-- ANCHOR_END: forces_neg

-- ANCHOR: monotone
/-- **Monotonicity.** What is forced stays forced in every future world. By
induction on the formula; the case of implication uses transitivity. -/
theorem Forces.mono (M : KripkeModel W) {w w' : W} (hle : w ≤ w') :
    ∀ A : Formula, Forces M w A → Forces M w' A
  | .var _, h => M.mono hle h
  | .top, _ => trivial
  | .bot, h => h
  | .and A B, ⟨hA, hB⟩ => ⟨Forces.mono M hle A hA, Forces.mono M hle B hB⟩
  | .or A _, .inl hA => .inl (Forces.mono M hle A hA)
  | .or _ B, .inr hB => .inr (Forces.mono M hle B hB)
  | .imp _ _, h => fun w'' hle' hA => h w'' (le_trans hle hle') hA
-- ANCHOR_END: monotone

-- ANCHOR: soundness
/-- **Soundness.** A derivable sequent is forced at every world of every
Kripke model that forces all of its assumptions. -/
theorem kripke_soundness {Γ : List Formula} {A : Formula} (h : Proves Γ A) :
    ∀ {W : Type} [Preorder W] (M : KripkeModel W) (w : W),
      (∀ B ∈ Γ, Forces M w B) → Forces M w A := by
  induction h with
  | hyp hmem => intro W _ M w hΓ; exact hΓ _ hmem
  | topI => intro W _ M w _; trivial
  | botE _ ih => intro W _ M w hΓ; exact (ih M w hΓ).elim
  | andI _ _ ih₁ ih₂ => intro W _ M w hΓ; exact ⟨ih₁ M w hΓ, ih₂ M w hΓ⟩
  | andE1 _ ih => intro W _ M w hΓ; exact (ih M w hΓ).1
  | andE2 _ ih => intro W _ M w hΓ; exact (ih M w hΓ).2
  | orI1 _ ih => intro W _ M w hΓ; exact .inl (ih M w hΓ)
  | orI2 _ ih => intro W _ M w hΓ; exact .inr (ih M w hΓ)
  | orE _ _ _ ih ihA ihB =>
    intro W _ M w hΓ
    rcases ih M w hΓ with hA | hB
    · apply ihA M w
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC
      · exact hA
      · exact hΓ C hC
    · apply ihB M w
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC
      · exact hB
      · exact hΓ C hC
  | impI _ ih =>
    -- To force A → B at w, take any future w' forcing A. The assumptions,
    -- forced at w, are still forced at w' (monotonicity), so the premise
    -- applies at w' with A added to the context.
    intro W _ M w hΓ w' hle hA
    apply ih M w'
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · exact hA
    · exact Forces.mono M hle C (hΓ C hC)
  | impE _ _ ih₁ ih₂ =>
    -- Use the implication at w itself, which is its own future (w ≤ w).
    intro W _ M w hΓ
    exact ih₁ M w hΓ w (le_refl w) (ih₂ M w hΓ)
-- ANCHOR_END: soundness

/-! ## Deciding forcing in finite models -/

-- ANCHOR: enumerable
/-- A type whose elements can be listed. (Mathlib's `Fintype` says the same,
but checking its instances by `decide` drags classical lemmas into the proof;
this small class keeps every result in this file constructive.) -/
class Enumerable (W : Type) where
  elems : List W
  complete : ∀ w, w ∈ elems

/-- Over an enumerable type, "for all `w`" is decidable: check every element
of the list. -/
instance decForallEnum {W : Type} [Enumerable W] (p : W → Prop) [DecidablePred p] :
    Decidable (∀ w, p w) :=
  decidable_of_iff (∀ w ∈ Enumerable.elems, p w)
    ⟨fun h w => h w (Enumerable.complete w), fun h w _ => h w⟩
-- ANCHOR_END: enumerable

-- ANCHOR: decidable
/-- In a finite model with a decidable order, forcing is decidable: every
quantifier ranges over finitely many worlds. -/
instance decForces [Enumerable W] [DecidableRel (α := W) (· ≤ ·)] (M : KripkeModel W) :
    ∀ (w : W) (A : Formula), Decidable (Forces M w A)
  | w, .var n => inferInstanceAs (Decidable (M.val w n = true))
  | _, .top => inferInstanceAs (Decidable True)
  | _, .bot => inferInstanceAs (Decidable False)
  | w, .and A B =>
    have := decForces M w A
    have := decForces M w B
    inferInstanceAs (Decidable (Forces M w A ∧ Forces M w B))
  | w, .or A B =>
    have := decForces M w A
    have := decForces M w B
    inferInstanceAs (Decidable (Forces M w A ∨ Forces M w B))
  | w, .imp A B =>
    have := fun w' => decForces M w' A
    have := fun w' => decForces M w' B
    inferInstanceAs (Decidable (∀ w', w ≤ w' → Forces M w' A → Forces M w' B))
-- ANCHOR_END: decidable

/-! ## The two-world countermodel -/

-- ANCHOR: stage
/-- Two stages of knowledge: `now`, and `later`, when we may know more. -/
inductive Stage where
  | now | later
  deriving DecidableEq

/-- `now ≤ later`, and each stage is below itself. -/
def Stage.le : Stage → Stage → Bool
  | .now, _ => true
  | .later, .later => true
  | .later, .now => false

instance : Preorder Stage where
  le a b := Stage.le a b = true
  le_refl a := by cases a <;> rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide

instance : DecidableRel (α := Stage) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (Stage.le a b = true))

instance : Enumerable Stage where
  elems := [.now, .later]
  complete w := by cases w <;> decide
-- ANCHOR_END: stage

-- ANCHOR: two_worlds
/-- Nothing is known `now`; `later`, the atom `P` (number 0) has been
established. -/
def twoWorlds : KripkeModel Stage where
  val
    | .later, 0 => true
    | _, _ => false
  mono {w w' n} hle hv := by
    change Stage.le w w' = true at hle
    cases w <;> cases w' <;> simp_all [Stage.le]
-- ANCHOR_END: two_worlds

-- ANCHOR: two_worlds_facts
/-- `P` is not forced now, but it will be. -/
example : ¬ Forces twoWorlds .now P ∧ Forces twoWorlds .later P := by decide

/-- `¬P` is not forced now either: a future world forces `P`. -/
example : ¬ Forces twoWorlds .now P.neg := by decide

/-- So excluded middle fails now. -/
theorem lem_fails : ¬ Forces twoWorlds .now (.or P P.neg) := by decide

/-- `¬¬P` holds now (`P` is never refuted), but `¬¬P → P` does not:
double-negation elimination fails. -/
theorem dne_fails : Forces twoWorlds .now P.neg.neg ∧
    ¬ Forces twoWorlds .now (.imp P.neg.neg P) := by decide

/-- Peirce's law `((P → Q) → P) → P` fails too (`Q` is never known). -/
theorem peirce_fails : ¬ Forces twoWorlds .now (.imp (.imp (.imp P Q) P) P) := by decide
-- ANCHOR_END: two_worlds_facts

-- ANCHOR: not_derivable
/-- Excluded middle is not derivable in the natural deduction of Chapter 4:
if it were, soundness would make it forced at `now`. -/
theorem lem_not_derivable : ¬ Proves [] (.or P P.neg) := by
  intro h
  exact lem_fails (kripke_soundness h twoWorlds .now (by simp))

theorem dne_not_derivable : ¬ Proves [] (.imp P.neg.neg P) := by
  intro h
  exact dne_fails.2 (kripke_soundness h twoWorlds .now (by simp))

theorem peirce_not_derivable : ¬ Proves [] (.imp (.imp (.imp P Q) P) P) := by
  intro h
  exact peirce_fails (kripke_soundness h twoWorlds .now (by simp))
-- ANCHOR_END: not_derivable

-- ANCHOR: not_derivable_axioms
-- The proof that excluded middle is not derivable is itself constructive.
/-- info: 'Ch05.lem_not_derivable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lem_not_derivable
-- ANCHOR_END: not_derivable_axioms

-- ANCHOR: incomplete
/-- Yet all three are tautologies: truth tables cannot tell them apart from
the derivable formulas. -/
example : isTautology 1 (.or P P.neg) = true ∧
    isTautology 1 (.imp P.neg.neg P) = true ∧
    isTautology 2 (.imp (.imp (.imp P Q) P) P) = true := by decide
-- ANCHOR_END: incomplete

/-! ## A fork: three worlds -/

-- ANCHOR: fork
/-- Three worlds: a root and two incomparable futures. -/
inductive Fork where
  | root | left | right
  deriving DecidableEq

/-- The order: the root is below everything, and each world is below itself. -/
def Fork.le : Fork → Fork → Bool
  | .root, _ => true
  | .left, .left => true
  | .right, .right => true
  | _, _ => false

instance : Preorder Fork where
  le a b := Fork.le a b = true
  le_refl a := by cases a <;> rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide

instance : DecidableRel (α := Fork) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (Fork.le a b = true))

instance : Enumerable Fork where
  elems := [.root, .left, .right]
  complete w := by cases w <;> decide

/-- `P` becomes known on the left branch, `Q` on the right branch. -/
def fork : KripkeModel Fork where
  val
    | .left, 0 => true
    | .right, 1 => true
    | _, _ => false
  mono {w w' n} hle hv := by
    change Fork.le w w' = true at hle
    cases w <;> cases w' <;> simp_all [Fork.le]
-- ANCHOR_END: fork

-- ANCHOR: fork_facts
/-- The De Morgan law `¬(P ∧ Q) → ¬P ∨ ¬Q` fails at the root. -/
theorem de_morgan_fails :
    ¬ Forces fork .root (.imp (Formula.and P Q).neg (.or P.neg Q.neg)) := by decide

/-- Weak excluded middle `¬P ∨ ¬¬P` fails at the root. -/
theorem wlem_fails : ¬ Forces fork .root (.or P.neg P.neg.neg) := by decide

theorem de_morgan_not_derivable : ¬ Proves [] (.imp (Formula.and P Q).neg (.or P.neg Q.neg)) :=
  fun h => de_morgan_fails (kripke_soundness h fork .root (by simp))
-- ANCHOR_END: fork_facts

/-! ## One world is a truth table -/

-- ANCHOR: one_world
/-- The only possible order on a one-element type. -/
local instance : Preorder Unit where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

/-- A model with a single world. -/
def oneWorld (v : Nat → Bool) : KripkeModel Unit where
  val _ n := v n
  mono _ h := h

/-- In a one-world model, forcing is truth-table evaluation: the quantifier
over futures has only the present to range over. -/
theorem forces_oneWorld (v : Nat → Bool) :
    ∀ A : Formula, Forces (oneWorld v) () A ↔ eval v A = true
  | .var _ => Iff.rfl
  | .top => by simp [Forces, eval]
  | .bot => by simp [Forces, eval]
  | .and A B => by
    simp [Forces, eval, ← forces_oneWorld v A, ← forces_oneWorld v B]
  | .or A B => by
    simp [Forces, eval, ← forces_oneWorld v A, ← forces_oneWorld v B]
  | .imp A B => by
    have hA := forces_oneWorld v A
    have hB := forces_oneWorld v B
    simp only [Forces, eval]
    cases h : eval v A <;> simp_all
-- ANCHOR_END: one_world

end Ch05
