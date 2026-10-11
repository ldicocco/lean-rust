import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

/-!
# Chapter 32 · A shallow separation logic

Heaps as partial maps from locations to values, assertions as predicates on
heaps, points-to and the separating conjunction, with its laws (commutativity,
associativity, `emp` as unit, monotonicity), the splitting of an array
points-to that justifies `split_at_mut`, and affinity: in the exact model
`P ∗ Q ⊢ P` fails, in the up-closed (affine) model it holds.
`Book.Ch32.Frame` adds commands, Hoare triples and the frame rule.
-/

namespace Ch32.Sep

/-! ## Heaps -/

-- ANCHOR: heap
/-- Memory locations. -/
abbrev Loc := ℕ
/-- The values stored in memory. -/
abbrev Val := ℤ

/-- A heap is a partial map from locations to values: `h l = none` means that
`l` is not allocated in `h`. -/
abbrev Heap := Loc → Option Val

/-- The empty heap. -/
def Heap.empty : Heap := fun _ => none

/-- The heap with exactly one allocated cell, `l`, holding `v`. -/
def Heap.single (l : Loc) (v : Val) : Heap :=
  fun l' => if l' = l then some v else none

/-- Two heaps are disjoint when no location is allocated in both. -/
def Heap.Disjoint (h₁ h₂ : Heap) : Prop := ∀ l, h₁ l = none ∨ h₂ l = none

/-- The union of two heaps (meant for disjoint heaps; if both define `l`, the
left one wins). -/
def Heap.union (h₁ h₂ : Heap) : Heap := fun l =>
  match h₁ l with
  | some v => some v
  | none => h₂ l

@[inherit_doc] scoped infixl:65 " ∪ₕ " => Heap.union
-- ANCHOR_END: heap

-- ANCHOR: finite
/-- A heap is finite when every location from some bound on is free. -/
def Heap.Finite (h : Heap) : Prop := ∃ n, ∀ l, n ≤ l → h l = none

/-- A finite heap always has a free location: this is what allocation needs. -/
theorem Heap.exists_free {h : Heap} (hf : h.Finite) : ∃ l, h l = none := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, hn n (Nat.le_refl n)⟩
-- ANCHOR_END: finite

theorem Heap.finite_union {h₁ h₂ : Heap} (f₁ : h₁.Finite) (f₂ : h₂.Finite) :
    (h₁ ∪ₕ h₂).Finite := by
  obtain ⟨n₁, hn₁⟩ := f₁
  obtain ⟨n₂, hn₂⟩ := f₂
  refine ⟨n₁ + n₂, fun l hl => ?_⟩
  simp only [Heap.union, hn₁ l (Nat.le_trans (Nat.le_add_right n₁ n₂) hl),
    hn₂ l (Nat.le_trans (Nat.le_add_left n₂ n₁) hl)]

namespace Heap

/-! Lemmas about union and disjointness. Each is a pointwise case analysis. -/

-- ANCHOR: union_assoc
theorem union_assoc (h₁ h₂ h₃ : Heap) : (h₁ ∪ₕ h₂) ∪ₕ h₃ = h₁ ∪ₕ (h₂ ∪ₕ h₃) := by
  funext l
  simp only [union]
  cases h₁ l <;> rfl
-- ANCHOR_END: union_assoc

theorem union_comm {h₁ h₂ : Heap} (hd : Disjoint h₁ h₂) : h₁ ∪ₕ h₂ = h₂ ∪ₕ h₁ := by
  funext l
  simp only [union]
  rcases hd l with h | h <;> simp only [h] <;> cases h₁ l <;> cases h₂ l <;> simp_all

theorem empty_union (h : Heap) : empty ∪ₕ h = h := rfl

theorem Disjoint.symm {h₁ h₂ : Heap} (hd : Disjoint h₁ h₂) : Disjoint h₂ h₁ :=
  fun l => (hd l).symm

theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :
    Disjoint (h₁ ∪ₕ h₂) h₃ ↔ Disjoint h₁ h₃ ∧ Disjoint h₂ h₃ := by
  constructor
  · intro hd
    constructor
    · intro l
      have := hd l
      simp only [union] at this
      cases e : h₁ l <;> simp_all
    · intro l
      have := hd l
      simp only [union] at this
      cases e : h₁ l <;> simp_all
  · rintro ⟨hd₁, hd₂⟩ l
    simp only [union]
    cases h : h₁ l with
    | none => exact hd₂ l
    | some v => exact Or.inr ((hd₁ l).resolve_left (by simp [h]))

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} :
    Disjoint h₁ (h₂ ∪ₕ h₃) ↔ Disjoint h₁ h₂ ∧ Disjoint h₁ h₃ := by
  constructor
  · intro hd
    have := (disjoint_union_left.mp hd.symm)
    exact ⟨this.1.symm, this.2.symm⟩
  · rintro ⟨hd₁, hd₂⟩
    exact (disjoint_union_left.mpr ⟨hd₁.symm, hd₂.symm⟩).symm

end Heap

open Heap

-- ANCHOR: heap_facts
/-- info: Ch32.Sep.Heap.union_comm {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) : h₁ ∪ₕ h₂ = h₂ ∪ₕ h₁ -/
#guard_msgs in
#check union_comm

/--
info: Ch32.Sep.Heap.disjoint_union_left {h₁ h₂ h₃ : Heap} : (h₁ ∪ₕ h₂).Disjoint h₃ ↔ h₁.Disjoint h₃ ∧ h₂.Disjoint h₃
-/
#guard_msgs in
#check disjoint_union_left
-- ANCHOR_END: heap_facts

/-! ## Assertions -/

-- ANCHOR: assertions
/-- An assertion is a property of heaps: the heaps it describes. -/
abbrev Assertion := Heap → Prop

/-- `emp`: the heap is empty. -/
def emp : Assertion := fun h => h = Heap.empty

/-- `l ↦ v`: the heap is exactly one cell, `l`, holding `v`. -/
def pointsTo (l : Loc) (v : Val) : Assertion := fun h => h = Heap.single l v

/-- `P ∗ Q`: the heap splits into two disjoint parts, one satisfying `P` and
the other satisfying `Q`. -/
def sep (P Q : Assertion) : Assertion := fun h =>
  ∃ h₁ h₂, Heap.Disjoint h₁ h₂ ∧ h = h₁ ∪ₕ h₂ ∧ P h₁ ∧ Q h₂

/-- `P ⊢ Q`: every heap described by `P` is described by `Q`. -/
def Entails (P Q : Assertion) : Prop := ∀ h, P h → Q h

@[inherit_doc] scoped infix:60 " ↦ " => pointsTo
@[inherit_doc] scoped infixr:35 " ∗ " => sep
@[inherit_doc] scoped infix:25 " ⊢ " => Entails
-- ANCHOR_END: assertions

/-! ## The laws of the separating conjunction -/

-- ANCHOR: sep_comm
theorem sep_comm (P Q : Assertion) : (P ∗ Q) = (Q ∗ P) := by
  funext h
  apply propext
  constructor
  all_goals
    rintro ⟨h₁, h₂, hd, rfl, hP, hQ⟩
    exact ⟨h₂, h₁, hd.symm, union_comm hd, hQ, hP⟩
-- ANCHOR_END: sep_comm

-- ANCHOR: sep_assoc
theorem sep_assoc (P Q R : Assertion) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  funext h
  apply propext
  constructor
  · rintro ⟨h₁₂, h₃, hd, rfl, ⟨h₁, h₂, hd₁₂, rfl, hP, hQ⟩, hR⟩
    obtain ⟨hd₁₃, hd₂₃⟩ := disjoint_union_left.mp hd
    exact ⟨h₁, h₂ ∪ₕ h₃, disjoint_union_right.mpr ⟨hd₁₂, hd₁₃⟩,
      union_assoc h₁ h₂ h₃, hP, h₂, h₃, hd₂₃, rfl, hQ, hR⟩
  · rintro ⟨h₁, h₂₃, hd, rfl, hP, ⟨h₂, h₃, hd₂₃, rfl, hQ, hR⟩⟩
    obtain ⟨hd₁₂, hd₁₃⟩ := disjoint_union_right.mp hd
    exact ⟨h₁ ∪ₕ h₂, h₃, disjoint_union_left.mpr ⟨hd₁₃, hd₂₃⟩,
      (union_assoc h₁ h₂ h₃).symm, ⟨h₁, h₂, hd₁₂, rfl, hP, hQ⟩, hR⟩
-- ANCHOR_END: sep_assoc

-- ANCHOR: emp_sep
theorem emp_sep (P : Assertion) : (emp ∗ P) = P := by
  funext h
  apply propext
  constructor
  · rintro ⟨_, h₂, _, rfl, rfl, hP⟩
    exact hP
  · intro hP
    exact ⟨Heap.empty, h, fun _ => Or.inl rfl, rfl, rfl, hP⟩
-- ANCHOR_END: emp_sep

-- ANCHOR: sep_mono
/-- Monotonicity: entailments can be applied inside either side of `∗`.
Reading it with `Q = Q'`: what `P` entails, `P ∗ Q` entails with the frame `Q`
untouched. -/
theorem sep_mono {P P' Q Q' : Assertion} (hP : P ⊢ P') (hQ : Q ⊢ Q') :
    (P ∗ Q) ⊢ (P' ∗ Q') := by
  rintro h ⟨h₁, h₂, hd, rfl, hp, hq⟩
  exact ⟨h₁, h₂, hd, rfl, hP h₁ hp, hQ h₂ hq⟩
-- ANCHOR_END: sep_mono

/-! ## Ownership is exclusive -/

-- ANCHOR: no_dup
/-- Nobody can own the same cell twice: `l ↦ v ∗ l ↦ w` describes no heap. -/
theorem pointsTo_sep_same (l : Loc) (v w : Val) :
    ((l ↦ v) ∗ (l ↦ w)) ⊢ fun _ => False := by
  rintro _ ⟨h₁, h₂, hd, _, rfl, rfl⟩
  rcases hd l with h | h <;> simp [Heap.single] at h
-- ANCHOR_END: no_dup

/-! ## Arrays, and the lemma behind `split_at_mut` -/

-- ANCHOR: ptArr
/-- `ptArr l [v₀, v₁, …]`: the cells `l, l+1, …` hold `v₀, v₁, …`. -/
def ptArr : Loc → List Val → Assertion
  | _, [] => emp
  | l, v :: vs => (l ↦ v) ∗ ptArr (l + 1) vs

/-- An array is the separating conjunction of its two parts. -/
theorem ptArr_append (xs ys : List Val) (l : Loc) :
    ptArr l (xs ++ ys) = (ptArr l xs ∗ ptArr (l + xs.length) ys) := by
  induction xs generalizing l with
  | nil => simp [ptArr, emp_sep]
  | cons x xs ih =>
    rw [List.cons_append, ptArr, ptArr, ih, sep_assoc, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1 xs.length]

/-- `split_at_mut`, in the logic: owning `vs` at `l` is the same as owning its
first `mid` elements at `l` and the rest at `l + mid`. -/
theorem ptArr_split (vs : List Val) (l mid : ℕ) (h : mid ≤ vs.length) :
    ptArr l vs = (ptArr l (vs.take mid) ∗ ptArr (l + mid) (vs.drop mid)) := by
  have := ptArr_append (vs.take mid) (vs.drop mid) l
  rwa [List.take_append_drop, List.length_take_of_le h] at this
-- ANCHOR_END: ptArr

/-! ## Affinity -/

-- ANCHOR: weakening_fails
/-- In this exact model, the separating conjunction cannot forget a part: the
heap with two cells satisfies `0 ↦ 1 ∗ 1 ↦ 2` but not `0 ↦ 1`. -/
theorem weakening_fails :
    ¬ (((0 : Loc) ↦ 1) ∗ ((1 : Loc) ↦ 2) ⊢ ((0 : Loc) ↦ 1)) := by
  intro hent
  have hd : Disjoint (Heap.single 0 1) (Heap.single 1 2) := by
    intro l
    by_cases hl : l = 0 <;> simp [Heap.single, hl]
  have h := hent _ ⟨_, _, hd, rfl, rfl, rfl⟩
  -- `h` claims the two-cell heap equals the one-cell heap; look at cell 1.
  have := congrFun h 1
  simp [Heap.union, Heap.single] at this
-- ANCHOR_END: weakening_fails

-- ANCHOR: extends
/-- `h ≤ₕ h'`: `h'` extends `h` (it has every cell of `h`, with the same value,
and possibly more). -/
def Heap.Extends (h h' : Heap) : Prop := ∀ l v, h l = some v → h' l = some v

@[inherit_doc] scoped infix:50 " ≤ₕ " => Heap.Extends

/-- An assertion is up-closed (affine) when adding cells to a heap that
satisfies it gives a heap that still satisfies it. -/
def UpClosed (P : Assertion) : Prop := ∀ h h', h ≤ₕ h' → P h → P h'

theorem Heap.extends_union_left (h₁ h₂ : Heap) : h₁ ≤ₕ (h₁ ∪ₕ h₂) := by
  intro l v hv
  simp [Heap.union, hv]
-- ANCHOR_END: extends

-- ANCHOR: sep_weaken
/-- Weakening, `P ∗ Q ⊢ P`, holds for every up-closed `P`. -/
theorem sep_weaken {P Q : Assertion} (hP : UpClosed P) : (P ∗ Q) ⊢ P := by
  rintro _ ⟨h₁, h₂, _, rfl, hp, _⟩
  exact hP h₁ (h₁ ∪ₕ h₂) (Heap.extends_union_left h₁ h₂) hp
-- ANCHOR_END: sep_weaken

-- ANCHOR: affine_pointsTo
/-- The affine points-to: the heap contains (at least) the cell `l` with `v`. -/
def pointsToA (l : Loc) (v : Val) : Assertion := fun h => h l = some v

theorem pointsToA_upClosed (l : Loc) (v : Val) : UpClosed (pointsToA l v) :=
  fun _ _ hext hp => hext l v hp

/-- Forgetting is allowed in the affine model. -/
example (l l' : Loc) (v v' : Val) :
    (pointsToA l v ∗ pointsToA l' v') ⊢ pointsToA l v :=
  sep_weaken (pointsToA_upClosed l v)

/-- Exclusive ownership survives: the same cell still cannot be owned twice. -/
theorem pointsToA_sep_same (l : Loc) (v w : Val) :
    (pointsToA l v ∗ pointsToA l w) ⊢ fun _ => False := by
  rintro _ ⟨h₁, h₂, hd, _, hv, hw⟩
  rcases hd l with h | h <;> simp_all [pointsToA]
-- ANCHOR_END: affine_pointsTo

-- ANCHOR: upClosed_sep
/-- If `Q` is up-closed, so is `P ∗ Q`, whatever `P` is: the extra cells go to
`Q`'s side. In particular the up-closed assertions are closed under `∗`, so the
affine assertions form a logic of their own. -/
theorem upClosed_sep {P Q : Assertion} (hQ : UpClosed Q) :
    UpClosed (P ∗ Q) := by
  rintro _ h' hext ⟨h₁, h₂, hd, rfl, hp, hq⟩
  -- Give `h₁` to `P` unchanged, and everything else of `h'` to `Q`.
  let h₂' : Heap := fun l => if (h₁ l).isSome then none else h' l
  refine ⟨h₁, h₂', ?_, ?_, hp, hQ h₂ h₂' ?_ hq⟩
  · -- `h₁` and `h₂'` are disjoint by construction.
    intro l
    by_cases h : (h₁ l).isSome <;> simp_all [h₂']
  · -- `h'` is the union of `h₁` and `h₂'`.
    funext l
    simp only [Heap.union, h₂']
    cases e : h₁ l with
    | none => simp
    | some v => exact hext l v (by simp [Heap.union, e])
  · -- `h₂'` extends `h₂`: the cells of `h₂` are not in `h₁`, and are in `h'`.
    intro l v hv
    have hn : h₁ l = none := (hd l).resolve_right (by simp [hv])
    have := hext l v (by simp [Heap.union, hn, hv])
    simp [h₂', hn, this]
-- ANCHOR_END: upClosed_sep

-- ANCHOR: upClosed_sep_check
/-- info: Ch32.Sep.upClosed_sep {P Q : Assertion} (hQ : UpClosed Q) : UpClosed (P ∗ Q) -/
#guard_msgs in
#check upClosed_sep
-- ANCHOR_END: upClosed_sep_check

end Ch32.Sep
