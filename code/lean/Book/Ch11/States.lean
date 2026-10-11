import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Book.Ch11.Iso
import Book.Ch11.Cardinality

/-!
# Chapter 11 · Counting illegal states

The two designs of `ch11_illegal_states.rs`, for an arbitrary finite type of
roles `R`: flags `Bool × Option R` with an invariant, and `Option R` (that is,
`1 + R`). The legal flags are isomorphic to `Option R`, and the flags have
exactly `|R| + 1` illegal states.
-/

namespace Ch11

open Ch11.Iso

variable {R : Type}

-- ANCHOR: legal
/-- The invariant of the flags design: a role exactly when connected. -/
def Legal : Bool × Option R → Prop
  | (connected, role) => connected = role.isSome

instance : DecidablePred (Legal (R := R)) :=
  fun s => inferInstanceAs (Decidable (s.1 = s.2.isSome))

/-- The legal flags, as a type: a *subtype*, the values of `Bool × Option R`
that come with a proof of `Legal`. -/
abbrev LegalFlags (R : Type) : Type := {s : Bool × Option R // Legal s}
-- ANCHOR_END: legal

-- ANCHOR: legal_iso
/-- The legal flags are isomorphic to `Option R`, i.e. to `1 + R`. -/
def legalIso (R : Type) : LegalFlags R ≅ Option R where
  toFun s := s.val.2
  invFun role := ⟨(role.isSome, role), rfl⟩
  left_inv := by
    intro ⟨⟨connected, role⟩, h⟩
    -- h : connected = role.isSome, so `connected` is determined by `role`
    simp only [Legal] at h
    subst h
    rfl
  right_inv _ := rfl
-- ANCHOR_END: legal_iso

-- ANCHOR: count
/-- The flags design has `2 * (|R| + 1)` states... -/
theorem card_flags [Fintype R] :
    Fintype.card (Bool × Option R) = 2 * (Fintype.card R + 1) := by
  simp

/-- ...of which `|R| + 1` are legal... -/
theorem card_legal [Fintype R] :
    Fintype.card (LegalFlags R) = Fintype.card R + 1 := by
  rw [card_eq_of_iso (legalIso R), Fintype.card_option]

/-- ...so exactly `|R| + 1` of them are illegal. -/
theorem card_illegal [Fintype R] :
    Fintype.card (Bool × Option R) - Fintype.card (LegalFlags R) =
      Fintype.card R + 1 := by
  rw [card_flags, card_legal]
  omega
-- ANCHOR_END: count

end Ch11
