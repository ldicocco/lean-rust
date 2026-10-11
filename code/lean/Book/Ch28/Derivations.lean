import Book.Ch28.Typing

/-!
# Chapter 28 · The two worked derivations

Derivation I (a `&mut` reference used twice through two reborrows) built as a
proof term; derivation II (the classic aliasing bug) shown to have no
derivation at all, first by inversion and then as a corollary of the usage
theorem; the escape check rejecting a dangling reference; and `Copy` at work on
a shared reference.
-/

namespace Ch28

-- ANCHOR: abbrev_m
/-- `M κ` abbreviates `&'κ mut Int`, as in the text. -/
abbrev M (κ : Lft) : Ty := .refMut κ .int
-- ANCHOR_END: abbrev_m

/-! ## Derivation I: a `&mut` reborrow -/

-- ANCHOR: twice
/-- The body of `fn twice<'a>(r: &'a mut i32)`: two writes through `r`, each
through a reborrow that hands `r` back under a new name.

    let (r1, u1) = borrow y1 = &'b1 mut *r in *y1 := 1 in
    let (r2, u2) = borrow y2 = &'b2 mut *r1 in *y2 := 2 in
    () -/
def twice : Term :=
  .letPair "r1" "u1" (.reborrow "b1" "y1" (.var "r") (.assign (.var "y1") (.lit 1)))
    (.letPair "r2" "u2" (.reborrow "b2" "y2" (.var "r1") (.assign (.var "y2") (.lit 2)))
      .unit)
-- ANCHOR_END: twice

-- ANCHOR: d1
/-- `𝒟₁`, the body of the first reborrow:
`'b1, 'a; y1 : &'b1 mut Int ⊢ *y1 := 1 : Unit`. -/
theorem d₁ :
    HasType ["b1", "a"] [("y1", M "b1")] (.assign (.var "y1") (.lit 1)) .unit :=
  .assign (.left .nil) (.var rfl) .lit
-- ANCHOR_END: d1

-- ANCHOR: e1
/-- The first reborrow, `E₁`, by rule T-Reborrow:
`'a; r : &'a mut Int ⊢ E₁ : &'a mut Int ⊗ Unit`. -/
theorem e₁ :
    HasType ["a"] [("r", M "a")]
      (.reborrow "b1" "y1" (.var "r") (.assign (.var "y1") (.lit 1)))
      (.pair (M "a") .unit) :=
  .reborrow
    (.left .nil)   -- split: `r` goes to the reborrowed expression
    (.var rfl)     -- 'a; r : &'a mut Int ⊢ r : &'a mut Int
    (by decide)    -- `y1` is a new variable
    d₁             -- the body, with 'b1 in scope
    (by decide)    -- freshness: 'b1 ∉ ['a]
    (by decide)    -- escape check: 'b1 ∉ flv(Unit)
-- ANCHOR_END: e1

-- ANCHOR: e2
/-- The second reborrow, `E₂`: the same derivation, for `r1` and `'b2`. -/
theorem e₂ :
    HasType ["a"] [("r1", M "a")]
      (.reborrow "b2" "y2" (.var "r1") (.assign (.var "y2") (.lit 2)))
      (.pair (M "a") .unit) :=
  .reborrow (.left .nil) (.var rfl) (by decide)
    (.assign (.left .nil) (.var rfl) .lit) (by decide) (by decide)
-- ANCHOR_END: e2

-- ANCHOR: twice_typed
/-- Derivation I: `'a; r : &'a mut Int ⊢ twice : Unit`. -/
theorem twice_typed : HasType ["a"] [("r", M "a")] twice .unit :=
  .letPair (.left .nil) e₁ (by decide) (by decide) (by decide)
    (.letPair (.left (.right .nil)) e₂ (by decide) (by decide) (by decide)
      .unit)
-- ANCHOR_END: twice_typed

-- ANCHOR: twice_occ
/-- `r` occurs exactly once in `twice`, in the first reborrow. -/
example : twice.occ "r" = 1 := by decide
-- ANCHOR_END: twice_occ

/-! ## Derivation II: the aliasing bug -/

-- ANCHOR: aliasing
/-- The classic aliasing bug, with `v : Box Int` standing for the vector:

    borrow f = &'a v in
      let (v2, u) = borrow m = &'b mut v in *m := 4 in
      *f -/
def aliasing : Term :=
  .borrow "a" "f" (.var "v")
    (.letPair "v2" "u" (.borrowMut "b" "m" (.var "v") (.assign (.var "m") (.lit 4)))
      (.deref (.var "f")))
-- ANCHOR_END: aliasing

-- ANCHOR: aliasing_untypable
/-- No derivation exists, whatever the lifetimes in scope and the result
type. The proof inverts the rules: each `cases` asks "which rule could have
produced this judgment, and with which premises?". -/
theorem aliasing_untypable (Δ : List Lft) (τ : Ty) :
    ¬ HasType Δ [("v", .box .int)] aliasing τ := by
  intro h
  -- Only T-Borrow concludes a shared borrow.
  cases h with
  | borrow hs hv _ hbody _ _ =>
    -- The context `v : Box Int` must be split between `v` and the body.
    cases hs with
    | both hc _ =>
      -- Give `v` to both sides? Only if `Box Int` were `Copy`.
      exact not_copy_box _ hc
    | right hs =>
      -- Give `v` to the body: the borrowed expression `v` has no context.
      cases hs
      have hmem := hv.var_mem
      simp [dom] at hmem
    | left hs =>
      -- Give `v` to the borrowed expression: the body only has `f`.
      cases hs
      cases hbody with
      | letPair hs₂ hbm _ _ _ _ =>
        cases hbm with
        | borrowMut hs₃ hv₃ _ _ _ _ =>
          -- The inner `&mut v` needs `v`, in a part of a part of `[f]`.
          have hmem :=
            dom_subset hs₂.sublist.1 (dom_subset hs₃.sublist.1 hv₃.var_mem)
          simp [dom] at hmem
-- ANCHOR_END: aliasing_untypable

-- ANCHOR: aliasing_corollary
/-- info: 2 -/
#guard_msgs in
#eval aliasing.occ "v"

/-- The same fact, as a corollary of the usage theorem: `v` occurs twice. -/
theorem aliasing_untypable' (Δ : List Lft) (τ : Ty) :
    ¬ HasType Δ [("v", .box .int)] aliasing τ := fun h =>
  have once : aliasing.occ "v" ≤ 1 :=
    h.used_at_most_once (by decide) rfl (not_copy_box .int)
  absurd once (by decide)
-- ANCHOR_END: aliasing_corollary

/-! ## The escape check -/

-- ANCHOR: escape
/-- A borrow whose body returns the reference itself:
`borrow y = &'a b in y`. -/
def escape : Term := .borrow "a" "y" (.var "b") (.var "y")

/-- Rejected by the escape check, and by nothing else. -/
theorem escape_untypable (Δ : List Lft) (τ : Ty) :
    ¬ HasType Δ [("b", .box .int)] escape τ := by
  intro h
  cases h with
  | borrow _ _ _ hbody _ hesc =>
    -- The body `y` has the type of `y` in its context: `&'a τ'`.
    cases hbody with
    | var hl =>
      simp [lookup] at hl
      subst hl
      -- So the escape check demands `'a ∉ flv(&'a τ')`, which is false.
      simp [Ty.lfts] at hesc
-- ANCHOR_END: escape

-- ANCHOR: escape_occ
/-- The usage theorem cannot explain this rejection: `b` is used once. -/
example : escape.occ "b" = 1 := by decide
-- ANCHOR_END: escape_occ

/-! ## `Copy` and the split -/

-- ANCHOR: copy_split
/-- A shared reference may go to both sides of a split: `(s, s)` is fine. -/
theorem shared_twice :
    HasType ["a"] [("s", .ref "a" .int)] (.pair (.var "s") (.var "s"))
      (.pair (.ref "a" .int) (.ref "a" .int)) :=
  .pair (.both .ref .nil) (.var rfl) (.var rfl)

/-- A mutable reference may not: `(r, r)` has no type at all. -/
theorem mut_twice_untypable (τ : Ty) :
    ¬ HasType ["a"] [("r", M "a")] (.pair (.var "r") (.var "r")) τ := fun h =>
  absurd (h.ref_mut_used_at_most_once (r := "r") (by decide) rfl) (by decide)
-- ANCHOR_END: copy_split

end Ch28
