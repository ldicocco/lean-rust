# Types, Proofs and Ownership

*Type Theory, Logic and Category Theory through Rust and Lean 4*

by Luciano Di Cocco

[![CI](https://github.com/ldicocco/types-proofs-ownership/actions/workflows/ci.yml/badge.svg)](https://github.com/ldicocco/types-proofs-ownership/actions/workflows/ci.yml)

A complete, hands-on course on type theory and its two closest relatives, logic
and category theory, for programmers who use **Rust** and want to understand
the ideas behind its type system. Every idea is presented three times: as
mathematics (rules, definitions, diagrams), in **Rust** (where the idea lives in a
production language, and where Rust deviates from the theory) and in **Lean 4**
(where the idea is stated precisely and every proof is checked by a machine).
The book builds up to a precise answer to a question that is often asked and
rarely answered: *are Rust's ownership and lifetimes really based on affine
types?*

No previous knowledge of Lean, type theory, logic or category theory is assumed.

- **Read the whole book:** [`book/Types-Proofs-and-Ownership.pdf`](book/Types-Proofs-and-Ownership.pdf)
- **Read chapter by chapter:** Markdown and PDF for every chapter in [`book/chapters/`](book/chapters/)
- **Run the code:** a Cargo workspace in [`code/rust/`](code/rust/) and a Lake project in [`code/lean/`](code/lean/)

## Contents

<!-- toc:start -->
[Preface](book/chapters/00-preface.md) ([PDF](book/chapters/00-preface.pdf))


**Part I — Foundations**

| | Chapter | Markdown | PDF |
|---|---|---|---|
| 1 | Two Languages, One Idea | [md](book/chapters/01-two-languages.md) | [pdf](book/chapters/01-two-languages.pdf) |
| 2 | Lean 4 for Rust Programmers | [md](book/chapters/02-lean-for-rust-programmers.md) | [pdf](book/chapters/02-lean-for-rust-programmers.pdf) |
| 3 | Judgments, Rules and Derivations | [md](book/chapters/03-judgments-rules.md) | [pdf](book/chapters/03-judgments-rules.pdf) |
| 4 | Natural Deduction | [md](book/chapters/04-natural-deduction.md) | [pdf](book/chapters/04-natural-deduction.pdf) |
| 5 | Intuitionism and the Meaning of Proof | [md](book/chapters/05-intuitionism.md) | [pdf](book/chapters/05-intuitionism.pdf) |
| 6 | The Structural Rules | [md](book/chapters/06-structural-rules.md) | [pdf](book/chapters/06-structural-rules.pdf) |

**Part II — Programs as Proofs**

| | Chapter | Markdown | PDF |
|---|---|---|---|
| 7 | The Lambda Calculus | [md](book/chapters/07-lambda-calculus.md) | [pdf](book/chapters/07-lambda-calculus.pdf) |
| 8 | The Simply Typed Lambda Calculus and Closures | [md](book/chapters/08-stlc-closures.md) | [pdf](book/chapters/08-stlc-closures.pdf) |
| 9 | Type Safety, Proved | [md](book/chapters/09-type-safety.md) | [pdf](book/chapters/09-type-safety.pdf) |
| 10 | The Curry–Howard Correspondence | [md](book/chapters/10-curry-howard.md) | [pdf](book/chapters/10-curry-howard.pdf) |
| 11 | Algebraic Data Types and the Algebra of Types | [md](book/chapters/11-algebraic-data-types.md) | [pdf](book/chapters/11-algebraic-data-types.pdf) |

**Part III — Abstraction**

| | Chapter | Markdown | PDF |
|---|---|---|---|
| 12 | Parametric Polymorphism | [md](book/chapters/12-parametric-polymorphism.md) | [pdf](book/chapters/12-parametric-polymorphism.pdf) |
| 13 | Type Inference | [md](book/chapters/13-type-inference.md) | [pdf](book/chapters/13-type-inference.pdf) |
| 14 | Traits, Type Classes and Dictionary Passing | [md](book/chapters/14-traits-type-classes.md) | [pdf](book/chapters/14-traits-type-classes.pdf) |
| 15 | Existential Types and Dynamic Dispatch | [md](book/chapters/15-existential-types.md) | [pdf](book/chapters/15-existential-types.pdf) |

**Part IV — Categories**

| | Chapter | Markdown | PDF |
|---|---|---|---|
| 16 | Categories for Programmers | [md](book/chapters/16-categories.md) | [pdf](book/chapters/16-categories.pdf) |
| 17 | Functors and Higher-Kinded Types | [md](book/chapters/17-functors-hkt.md) | [pdf](book/chapters/17-functors-hkt.pdf) |
| 18 | Natural Transformations and Free Theorems | [md](book/chapters/18-natural-transformations.md) | [pdf](book/chapters/18-natural-transformations.pdf) |
| 19 | Cartesian Closed Categories | [md](book/chapters/19-cartesian-closed.md) | [pdf](book/chapters/19-cartesian-closed.pdf) |
| 20 | Monads and Effects | [md](book/chapters/20-monads.md) | [pdf](book/chapters/20-monads.pdf) |

**Part V — Ownership as Logic**

| | Chapter | Markdown | PDF |
|---|---|---|---|
| 21 | Substructural Logics | [md](book/chapters/21-substructural-logics.md) | [pdf](book/chapters/21-substructural-logics.pdf) |
| 22 | The Affine Lambda Calculus | [md](book/chapters/22-affine-lambda.md) | [pdf](book/chapters/22-affine-lambda.pdf) |
| 23 | Copy, Clone and the Exponential | [md](book/chapters/23-copy-clone-exponential.md) | [pdf](book/chapters/23-copy-clone-exponential.pdf) |
| 24 | Drop: Weakening with a Side Effect | [md](book/chapters/24-drop.md) | [pdf](book/chapters/24-drop.pdf) |
| 25 | Typestate: Protocols in Types | [md](book/chapters/25-typestate.md) | [pdf](book/chapters/25-typestate.pdf) |

**Part VI — Borrowing and Regions**

| | Chapter | Markdown | PDF |
|---|---|---|---|
| 26 | References, Aliasing and Regions | [md](book/chapters/26-references-regions.md) | [pdf](book/chapters/26-references-regions.pdf) |
| 27 | Subtyping and Variance | [md](book/chapters/27-subtyping-variance.md) | [pdf](book/chapters/27-subtyping-variance.pdf) |
| 28 | A Core Calculus for Borrowing | [md](book/chapters/28-core-borrow-calculus.md) | [pdf](book/chapters/28-core-borrow-calculus.pdf) |
| 29 | How rustc Really Checks Borrows | [md](book/chapters/29-rustc-borrow-checking.md) | [pdf](book/chapters/29-rustc-borrow-checking.pdf) |

**Part VII — Beyond**

| | Chapter | Markdown | PDF |
|---|---|---|---|
| 30 | Dependent Types | [md](book/chapters/30-dependent-types.md) | [pdf](book/chapters/30-dependent-types.pdf) |
| 31 | Proving Programs Correct | [md](book/chapters/31-proving-programs.md) | [pdf](book/chapters/31-proving-programs.pdf) |
| 32 | Soundness, unsafe and Semantic Types | [md](book/chapters/32-soundness-semantic-types.md) | [pdf](book/chapters/32-soundness-semantic-types.pdf) |
| 33 | The Verdict | [md](book/chapters/33-the-verdict.md) | [pdf](book/chapters/33-the-verdict.pdf) |

**Appendices**

| | Chapter | Markdown | PDF |
|---|---|---|---|
| A | Setting Up Rust and Lean | [md](book/chapters/A-setup.md) | [pdf](book/chapters/A-setup.pdf) |
| B | Lean 4 for Rust Programmers: Cheat Sheet | [md](book/chapters/B-lean-cheat-sheet.md) | [pdf](book/chapters/B-lean-cheat-sheet.pdf) |
| C | Notation and Dictionary | [md](book/chapters/C-notation.md) | [pdf](book/chapters/C-notation.pdf) |
| D | The Tactics Used in This Book | [md](book/chapters/D-tactics.md) | [pdf](book/chapters/D-tactics.pdf) |
| E | Glossary | [md](book/chapters/E-glossary.md) | [pdf](book/chapters/E-glossary.pdf) |
| F | Further Reading | [md](book/chapters/F-further-reading.md) | [pdf](book/chapters/F-further-reading.pdf) |
<!-- toc:end -->

## Running the code

Both toolchains are pinned: Rust 1.99.0 (`code/rust/rust-toolchain.toml`) and
Lean 4.34.1 (`code/lean/lean-toolchain`). With [rustup](https://rustup.rs) and
[elan](https://github.com/leanprover/elan) installed, the right versions are
downloaded on first use. The Rust code uses only the standard library. The Lean
code uses [Mathlib](https://github.com/leanprover-community/mathlib4), pinned to
the matching release; fetch its prebuilt files once (under 1 GB to download, about
8 GB on disk) before the first build.

```sh
cd code/rust
cargo run --example ch01_first_types         # single-file examples: examples/chNN_*.rs
cargo run -p stlc --example ch08_stlc        # examples that use one of the crates
cargo test -p arith                          # the crates' test suites

cd ../lean
lake exe cache get                           # once: download prebuilt Mathlib
lake build                                   # check every definition and proof
```

To verify everything the book shows (every example and its output, every
program that must be rejected and its diagnostics, every Lean file):

```sh
python3 tools/run_examples.py            # add --tests to run the crates' tests too
python3 tools/run_examples.py --only ch08
```

## Repository layout

```text
book/
  src/            chapter sources (Markdown with {{#include}} directives) + SUMMARY.md
  chapters/       generated: one .md and one .pdf per chapter, code inlined
  diagrams/       Graphviz sources of the diagrams; images/ has the rendered SVGs
  Types-Proofs-and-Ownership.pdf   generated: the complete book
  OUTLINE.md      the course outline (scope of every chapter)
code/
  rust/           Cargo workspace
    examples/       single-file examples (chNN_*.rs)
    crates/         the toy languages and tools built in the book
    compile_fail/   programs that must be rejected, with their diagnostics
    output/         snapshots of the examples' output, included in the book
  lean/           Lake project (depends on Mathlib): Book/ChNN/*.lean
tools/
  build_book.py   check / md / diagrams / pdf / readme / all
  run_examples.py verify every program, diagnostic and proof (--bless to update snapshots)
  AUTHORING.md    conventions used to write the course
```

## Rebuilding the book

The chapter Markdown in `book/src/` includes code directly from the sources, so
the text always shows the code that compiles. To regenerate the per-chapter
Markdown, the PDFs and this README's table of contents:

```sh
python3 tools/build_book.py check    # validate includes, anchors, math and image links
python3 tools/build_book.py all      # diagrams + chapters/*.md + PDFs + README toc
```

Requirements: Python 3.11+, [pandoc](https://pandoc.org) 3.x,
[Typst](https://typst.app) 0.13+ and Graphviz (`dot`).

## License

- **Code** (`code/` and `tools/`): available under either the
  [MIT license](LICENSE-MIT) or the [Apache License 2.0](LICENSE-APACHE), at your
  option.
- **Book** (`book/`: text, diagrams, images and the generated Markdown and PDFs):
  licensed under [CC BY-NC-SA 4.0](book/LICENSE). Code excerpts in the book come
  from `code/` and are also available under the code license.

This book is an independent work and is not affiliated with the Rust project or
the Lean FRO.
