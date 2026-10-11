import Book.Ch14.Monoid

/-!
# Chapter 14 · Walkthrough: statistics of measurements

Summary statistics (count, total, minimum, maximum) as a product of four
lawful monoids. The `LawfulMonoid` instance for the product comes for free
from `instLawfulProd`, and `mconcat_batches` then proves that computing the
statistics batch by batch and merging gives the same result as one pass, for
every input.
-/

namespace Ch14

open Monoid

-- ANCHOR: int_monoid
instance instMonoidInt : Monoid Int where
  empty := 0
  combine a b := a + b

instance instLawfulInt : LawfulMonoid Int where
  toMonoid := instMonoidInt
  combine_assoc := Int.add_assoc
  empty_combine := Int.zero_add
  combine_empty := Int.add_zero
-- ANCHOR_END: int_monoid

-- ANCHOR: low_high
/-- Combine two optional values with `f`; `none` means "no value yet" and is
the neutral element. -/
def merge (f : Int → Int → Int) : Option Int → Option Int → Option Int
  | none, y => y
  | x, none => x
  | some x, some y => some (f x y)

/-- The smallest value seen so far. -/
structure Low where
  val : Option Int

/-- The largest value seen so far. -/
structure High where
  val : Option Int

instance : Monoid Low where
  empty := ⟨none⟩
  combine a b := ⟨merge min a.val b.val⟩

instance : Monoid High where
  empty := ⟨none⟩
  combine a b := ⟨merge max a.val b.val⟩
-- ANCHOR_END: low_high

-- ANCHOR: low_high_lawful
-- The parent field `toMonoid` is omitted: resolution finds the instance above.
instance : LawfulMonoid Low where
  combine_assoc := by
    -- Eight cases: each of the three values is `none` or `some _`.
    rintro ⟨_ | x⟩ ⟨_ | y⟩ ⟨_ | z⟩ <;> simp [Monoid.combine, merge] <;> omega
  empty_combine := by rintro ⟨_ | x⟩ <;> rfl
  combine_empty := by rintro ⟨_ | x⟩ <;> rfl

instance : LawfulMonoid High where
  combine_assoc := by
    rintro ⟨_ | x⟩ ⟨_ | y⟩ ⟨_ | z⟩ <;> simp [Monoid.combine, merge] <;> omega
  empty_combine := by rintro ⟨_ | x⟩ <;> rfl
  combine_empty := by rintro ⟨_ | x⟩ <;> rfl
-- ANCHOR_END: low_high_lawful

instance : Repr Low where
  reprPrec l _ := match l.val with
    | none => "min -"
    | some x => s!"min {x}"

instance : Repr High where
  reprPrec h _ := match h.val with
    | none => "max -"
    | some x => s!"max {x}"

-- ANCHOR: stats
/-- Count, total, minimum and maximum: a product of four monoids. -/
abbrev Stats := Nat × Int × Low × High

/-- The statistics of a single measurement. -/
def Stats.of (x : Int) : Stats := (1, x, ⟨some x⟩, ⟨some x⟩)

/-- info: instLawfulProd -/
#guard_msgs in
#synth LawfulMonoid Stats
-- ANCHOR_END: stats

-- ANCHOR: stats_eval
/-- The measurements of the Rust walkthrough, in tenths of a degree. -/
def batches : List (List Int) :=
  [[215, 218, 221, 219], [202, 199], [230, 228, 233]]

/--
info: [(4, 873, min 215, max 221), (2, 401, min 199, max 202), (3, 691, min 228, max 233)]
-/
#guard_msgs in
#eval batches.map (fun b => mconcat (b.map Stats.of))

/-- info: (9, 1965, min 199, max 233) -/
#guard_msgs in
#eval mconcat (batches.map (fun b => mconcat (b.map Stats.of)))
-- ANCHOR_END: stats_eval

-- ANCHOR: stats_theorem
/-- Merging per-batch statistics gives the statistics of all the data,
for every list of batches. -/
theorem stats_by_batch (bs : List (List Int)) :
    mconcat (bs.map (fun b => mconcat (b.map Stats.of)))
      = mconcat (bs.flatten.map Stats.of) := by
  -- Mapping over a flattened list = flattening the mapped batches.
  rw [List.map_flatten]
  -- mconcat of a flattened list = mconcat of the batch results.
  rw [← mconcat_batches]
  -- Two consecutive maps are one map of the composite function.
  rw [List.map_map]
  -- Both sides now apply the same function to every batch.
  rfl
-- ANCHOR_END: stats_theorem

end Ch14
