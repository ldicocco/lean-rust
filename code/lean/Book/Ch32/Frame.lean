import Book.Ch32.SeparationLogic

/-!
# Chapter 32 · Hoare triples and the frame rule

A tiny command language over the heaps of `Book.Ch32.SeparationLogic`
(write, free, swap and sequencing; a command faults when it touches an
unallocated cell), Hoare triples that promise "no fault, and the
postcondition holds", small specifications for each command, and the frame
rule, proved from the locality of the commands.
-/

namespace Ch32.Sep

open Heap

-- ANCHOR: cmd
/-- Commands. -/
inductive Cmd where
  | skip
  | write (l : Loc) (v : Val)   -- `*l = v`
  | free (l : Loc)              -- deallocate `l`
  | swap (l₁ l₂ : Loc)          -- exchange the contents of `l₁` and `l₂`
  | seq (c₁ c₂ : Cmd)           -- `c₁; c₂`

/-- Change one cell of a heap (`none` deallocates it). -/
def Heap.update (h : Heap) (l : Loc) (o : Option Val) : Heap :=
  fun l' => if l' = l then o else h l'

/-- Run a command. `none` is a fault: the command touched a cell it does not
have. -/
def exec : Cmd → Heap → Option Heap
  | .skip, h => some h
  | .write l v, h => if (h l).isSome then some (h.update l (some v)) else none
  | .free l, h => if (h l).isSome then some (h.update l none) else none
  | .swap l₁ l₂, h =>
    match h l₁, h l₂ with
    | some a, some b => some ((h.update l₁ (some b)).update l₂ (some a))
    | _, _ => none
  | .seq c₁ c₂, h =>
    match exec c₁ h with
    | some h' => exec c₂ h'
    | none => none
-- ANCHOR_END: cmd

-- ANCHOR: triple
/-- The Hoare triple `{P} c {Q}`: from every heap satisfying `P`, the command
runs without fault and ends in a heap satisfying `Q`. -/
def Triple (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ h, P h → ∃ h', exec c h = some h' ∧ Q h'
-- ANCHOR_END: triple

/-! ## Locality: commands only touch what they own -/

-- ANCHOR: update_union
/-- Updating a cell that the frame does not have commutes with adding the
frame. -/
theorem update_union {h hf : Heap} {l : Loc} (o : Option Val) (hl : hf l = none) :
    (h ∪ₕ hf).update l o = h.update l o ∪ₕ hf := by
  funext l'
  by_cases e : l' = l
  · subst e
    cases o <;> simp [Heap.update, Heap.union, hl]
  · simp [Heap.update, Heap.union, e]
-- ANCHOR_END: update_union

theorem disjoint_update {h hf : Heap} {l : Loc} (o : Option Val)
    (hd : Disjoint h hf) (hl : hf l = none) : Disjoint (h.update l o) hf := by
  intro l'
  by_cases e : l' = l
  · subst e; exact Or.inr hl
  · simp only [Heap.update, e, ite_false]; exact hd l'

/-- A cell allocated in `h` is free in any heap disjoint from `h`. -/
theorem free_in_frame {h hf : Heap} {l : Loc} {v : Val} (hd : Disjoint h hf)
    (hv : h l = some v) : hf l = none :=
  (hd l).resolve_left (by simp [hv])

-- ANCHOR: write_local
/-- Locality of `write`: if it runs without fault in `h`, it runs the same way
in `h` plus a disjoint frame `hf`, and leaves the frame alone. -/
theorem write_local {h h' hf : Heap} {l : Loc} {v : Val} (hd : Disjoint h hf)
    (he : exec (.write l v) h = some h') :
    Disjoint h' hf ∧ exec (.write l v) (h ∪ₕ hf) = some (h' ∪ₕ hf) := by
  simp only [exec] at he
  split at he
  · -- The write did not fault, so `l` is allocated in `h`, holding some `a`.
    rename_i hs
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    -- Then the frame does not have `l`.
    have hl := free_in_frame hd ha
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨disjoint_update _ hd hl, ?_⟩
    simp [exec, Heap.union, ha, update_union _ hl]
  · -- The write faulted: `none = some h'` is impossible.
    simp at he
-- ANCHOR_END: write_local

theorem free_local {h h' hf : Heap} {l : Loc} (hd : Disjoint h hf)
    (he : exec (.free l) h = some h') :
    Disjoint h' hf ∧ exec (.free l) (h ∪ₕ hf) = some (h' ∪ₕ hf) := by
  simp only [exec] at he
  split at he
  · rename_i hs
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    have hl := free_in_frame hd ha
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨disjoint_update _ hd hl, ?_⟩
    simp [exec, Heap.union, ha, update_union _ hl]
  · simp at he

theorem swap_local {h h' hf : Heap} {l₁ l₂ : Loc} (hd : Disjoint h hf)
    (he : exec (.swap l₁ l₂) h = some h') :
    Disjoint h' hf ∧ exec (.swap l₁ l₂) (h ∪ₕ hf) = some (h' ∪ₕ hf) := by
  simp only [exec] at he
  split at he
  · rename_i a b ha hb
    have hl₁ := free_in_frame hd ha
    have hl₂ := free_in_frame hd hb
    simp only [Option.some.injEq] at he
    subst he
    refine ⟨disjoint_update _ (disjoint_update _ hd hl₁) hl₂, ?_⟩
    simp [exec, Heap.union, ha, hb, update_union _ hl₁, update_union _ hl₂]
  · simp at he

-- ANCHOR: exec_frame
/-- Locality of every command, by recursion on the command. -/
theorem exec_frame : ∀ (c : Cmd) {h h' hf : Heap}, Disjoint h hf →
    exec c h = some h' → Disjoint h' hf ∧ exec c (h ∪ₕ hf) = some (h' ∪ₕ hf)
  | .skip, _, _, _, hd, he => by
    simp only [exec, Option.some.injEq] at he
    subst he
    exact ⟨hd, rfl⟩
  | .write _ _, _, _, _, hd, he => write_local hd he
  | .free _, _, _, _, hd, he => free_local hd he
  | .swap _ _, _, _, _, hd, he => swap_local hd he
  | .seq c₁ c₂, _, _, _, hd, he => by
    simp only [exec] at he
    split at he
    · -- `c₁` ran to some `hmid` (`he₁`), then `c₂` ran from `hmid` (`he`).
      rename_i hmid he₁
      obtain ⟨hd₁, he₁'⟩ := exec_frame c₁ hd he₁
      obtain ⟨hd₂, he₂'⟩ := exec_frame c₂ hd₁ he
      exact ⟨hd₂, by simp [exec, he₁', he₂']⟩
    · simp at he
-- ANCHOR_END: exec_frame

-- ANCHOR: frame_rule
/-- The frame rule: a triple about a small heap holds in any larger heap, with
the extra part `R` carried through unchanged. -/
theorem frame {P Q R : Assertion} {c : Cmd} (h : Triple P c Q) :
    Triple (P ∗ R) c (Q ∗ R) := by
  rintro _ ⟨h₁, h₂, hd, rfl, hp, hr⟩
  obtain ⟨h₁', he, hq⟩ := h h₁ hp
  obtain ⟨hd', he'⟩ := exec_frame c hd he
  exact ⟨h₁' ∪ₕ h₂, he', h₁', h₂, hd', rfl, hq, hr⟩
-- ANCHOR_END: frame_rule

/-! ## Structural rules for triples -/

-- ANCHOR: seq_rule
theorem seq_rule {P Q R : Assertion} {c₁ c₂ : Cmd}
    (h₁ : Triple P c₁ Q) (h₂ : Triple Q c₂ R) : Triple P (.seq c₁ c₂) R := by
  intro h hp
  obtain ⟨h', e₁, hq⟩ := h₁ h hp
  obtain ⟨h'', e₂, hr⟩ := h₂ h' hq
  exact ⟨h'', by simp [exec, e₁, e₂], hr⟩

theorem consequence {P P' Q Q' : Assertion} {c : Cmd}
    (hP : P' ⊢ P) (h : Triple P c Q) (hQ : Q ⊢ Q') : Triple P' c Q' := by
  intro s hp
  obtain ⟨s', e, hq⟩ := h s (hP s hp)
  exact ⟨s', e, hQ s' hq⟩
-- ANCHOR_END: seq_rule

/-! ## Small specifications -/

-- ANCHOR: write_spec
/-- Writing needs the cell, and only the cell. -/
theorem write_spec (l : Loc) (a v : Val) : Triple (l ↦ a) (.write l v) (l ↦ v) := by
  rintro _ rfl
  refine ⟨(Heap.single l a).update l (some v), by simp [exec, Heap.single], ?_⟩
  funext l'
  by_cases e : l' = l <;> simp [Heap.update, Heap.single, e]
-- ANCHOR_END: write_spec

/-- Freeing gives the cell back: afterwards we own nothing. -/
theorem free_spec (l : Loc) (a : Val) : Triple (l ↦ a) (.free l) emp := by
  rintro _ rfl
  refine ⟨(Heap.single l a).update l none, by simp [exec, Heap.single], ?_⟩
  funext l'
  by_cases e : l' = l <;> simp [Heap.update, Heap.single, Heap.empty, e]

/-- Swapping two cells: the precondition owns both, separately. -/
theorem swap_spec (l₁ l₂ : Loc) (a b : Val) :
    Triple ((l₁ ↦ a) ∗ (l₂ ↦ b)) (.swap l₁ l₂) ((l₁ ↦ b) ∗ (l₂ ↦ a)) := by
  rintro _ ⟨_, _, hd, rfl, rfl, rfl⟩
  -- The two cells are different, because the two heaps are disjoint.
  have hne : l₂ ≠ l₁ := by
    intro e
    subst e
    rcases hd l₂ with h | h <;> simp [Heap.single] at h
  refine ⟨((Heap.single l₁ a ∪ₕ Heap.single l₂ b).update l₁ (some b)).update l₂
    (some a), by simp [exec, Heap.union, Heap.single, hne], ?_⟩
  refine ⟨Heap.single l₁ b, Heap.single l₂ a, ?_, ?_, rfl, rfl⟩
  · intro l
    by_cases e : l = l₁ <;> simp [Heap.single, e, Ne.symm hne]
  · funext l
    by_cases e₁ : l = l₁ <;> by_cases e₂ : l = l₂ <;>
      simp_all [Heap.update, Heap.union, Heap.single]

-- ANCHOR: spec_statements
/-- info: Ch32.Sep.free_spec (l : Loc) (a : Val) : Triple (l ↦ a) (Cmd.free l) emp -/
#guard_msgs in
#check free_spec

/--
info: Ch32.Sep.swap_spec (l₁ l₂ : Loc) (a b : Val) : Triple (l₁ ↦ a ∗ l₂ ↦ b) (Cmd.swap l₁ l₂) (l₁ ↦ b ∗ l₂ ↦ a)
-/
#guard_msgs in
#check swap_spec
-- ANCHOR_END: spec_statements

/-! ## Putting it together -/

-- ANCHOR: three_cells
/-- Three cells; swap the first two, then clear the third. Each step is proved
with its small specification, and the frame rule supplies the cells that the
step does not touch. -/
theorem three_cells :
    Triple ((0 ↦ 10) ∗ (1 ↦ 20) ∗ (2 ↦ 30))
      (.seq (.swap 0 1) (.write 2 0))
      ((0 ↦ 20) ∗ (1 ↦ 10) ∗ (2 ↦ 0)) := by
  apply seq_rule (Q := (0 ↦ 20) ∗ (1 ↦ 10) ∗ (2 ↦ 30))
  · -- The swap owns cells 0 and 1; cell 2 is the frame.
    have h := frame (R := 2 ↦ 30) (swap_spec 0 1 10 20)
    rw [sep_assoc, sep_assoc] at h
    exact h
  · -- The write owns cell 2; cells 0 and 1 are the frame.
    have h := frame (R := (0 ↦ 20) ∗ (1 ↦ 10)) (write_spec 2 30 0)
    rw [sep_comm (2 ↦ 30), sep_comm (2 ↦ 0), sep_assoc, sep_assoc] at h
    exact h
-- ANCHOR_END: three_cells

end Ch32.Sep
