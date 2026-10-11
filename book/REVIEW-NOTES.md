# Review notes for the next iteration

Working notes collected while the first edition was written. They are not part of
the book; delete this file before publishing, or keep it as an issue list.

## Notation that differs between chapters

The chapters were written in parallel, and a few conventions drifted. Appendix C
documents every variant, so nothing is wrong for the reader, but unifying them
would make the book read more smoothly.

1. **Substitution.** Terms: $t[x := s]$ in Chapters 7, 8, 15; $t[s/x]$ in
   Chapters 4, 6, 12, 19, 22, 23, 28, 30 (Chapter 7 mentions both). Types:
   $\tau[\sigma/\alpha]$ in Chapters 12, 18; $\tau[\alpha := \sigma]$ in Chapters
   14, 15.
2. **Rule names.** The λ rule is T-Lam in Chapters 8–10 and T-Abs in Chapters
   12–13 (check the crates' derivation printers and the Lean constructor names if
   you rename). The `!` rules are Der, !W, !C, Prom in Chapter 21 and
   Dereliction, !-Weak, !-Contr, Promotion in Chapter 23.
3. **Overloaded rule prefixes.** E- is evaluation, but entailment in Chapter 14.
   S- is synthesis (8), splitting (22, 23, 28) and subtyping (27). C- is checking
   (8) and `Copy` (28). R- is region rules (26) and NLL constraints (29).
4. **Overloaded symbols.** ⊩ is Kripke forcing (5) and constraint entailment (14);
   ⊣ is adjunction (19) and leftover context (22, 26); $\mathcal{C}$ is a category,
   but the set of `Copy` base types in Chapter 23; ρ is an environment, a type, a
   renaming and a region in different chapters.
5. **Typography.** $\mathcal{C}^{\mathrm{op}}$ (16–17) vs $\mathcal{C}^{op}$ (18,
   27); projections fst/snd (16) vs π₁/π₂ (19).
6. **Terminology.** "Inductive family" (6, 10) vs "indexed family" (25, 27).

## Polish

- **Length.** Most chapters have 8,000–9,000 words of prose, above the
  5,000–8,000 target of `tools/AUTHORING.md`; the book is 1,126 pages. A trimming
  pass would help readers, especially in Chapters 2, 11, 14, 16 and 22.
- **Diagnostics without an error code** can now be snapshotted
  (`// harness: compile-fail "message text"`, see AUTHORING.md). Candidates:
  - Chapter 27: the typical variance error, "lifetime may not live long enough"
    (the chapter currently uses E0597/E0521 variants);
  - Chapter 24: the `#[must_use]` lint, made an error with
    `#![deny(unused_must_use)]` (currently quoted in prose only);
  - Chapter 30: "generic parameters may not be used in const operations"
    (`ch30_const_arithmetic.rs` lists E0770 as a workaround).
- **Glossary headings** render as "E.1 A", "E.2 B" because appendix H2 headings
  are numbered by the template; consider unnumbered headings for Appendix E.
- **Toolchain-sensitive outputs.** Some `#guard_msgs` blocks contain metavariable
  numbers (`?m.5`) or line numbers (Chapter 31 mentions "line 61" of
  `Termination.lean`). They are exact for Lean 4.34.1 and will need refreshing
  when the toolchain is updated.
- **Polonius status** (Chapter 29) was checked against a nightly of October 2026;
  re-check before publishing.

## Before publishing

- `git init`, review `git status`, commit.
- Adjust the CI badge in README.md if the repository is not
  `ldicocco/types-proofs-ownership`.
- Run `python3 tools/run_examples.py --tests` and `python3 tools/build_book.py all`
  once more.
