# Authoring guide — *Types, Proofs and Ownership*

These are the conventions the course was written with. Follow them when you fix,
extend or update a chapter, so that the book stays consistent. The course outline
in `book/OUTLINE.md` defines the scope of every chapter (numbers, topics, file
names). The README explains how to build the book and run the code.

---

## 1. The reader and the tone

- The reader **uses Rust actively** (ownership and borrowing, structs and enums,
  traits and generics, closures, iterators, `Result`, Cargo) but is **not a Rust
  expert**. Do not assume they know variance, higher-ranked trait bounds,
  generic associated types, `PhantomData`, `unsafe` invariants, MIR or the
  details of the borrow checker. When the text uses such a feature, explain it.
- The reader knows **very little Lean, type theory, logic or category theory**,
  but has a **very active interest** in them: they want real definitions, real
  rules and real proofs, not a watered-down tour. Never use a concept before it
  is introduced; never skip a step in a proof that a beginner could not fill in.
  Every Lean feature is explained the first time it appears (or points back to
  the chapter that explains it).
- **Why before how.** Before a definition, say what problem it solves. After a
  rule, say what it means in plain words and where it shows up in Rust. Prefer
  one well-chosen example worked out completely over three sketched ones.
- **Three views of every idea.** Most sections move through the same steps:
  1. the mathematics: syntax, judgments, inference rules, definitions, diagrams;
  2. Rust: where the idea lives in a language the reader uses every day, and
     where Rust deviates from the clean theory (this is often the most
     interesting part);
  3. Lean: the idea stated precisely and checked by a machine: definitions,
     theorems and proofs. Rust *implements*; Lean *proves*.
  Not every section needs all three, but every chapter does.
- Connect new ideas to things the reader knows: compilers and linters, unit
  tests and property tests, interfaces, database constraints, state machines,
  resource management, API design.
- Introduce a concept with a minimal snippet, then build up. Never drop a long
  listing without a walkthrough; explain every non-obvious line, including every
  tactic in a proof.
- No games, no hype, no filler, no emojis, no HTML. Voice: clear, friendly,
  precise, second person ("you"), American spelling. Use "we" for things we do
  together ("we now prove...").
- Be honest about the limits of the analogy. The book's motto is the
  correspondence symbol $\approx$: "corresponds to, with caveats that the text
  states". Rust has no official formal semantics; when the text writes a typing
  rule "for Rust" it is a *model* of the compiler's behavior, and it should say
  so the first time it matters in a chapter.

## 2. Accuracy

1. **Every Rust snippet that claims to be working code comes from a file that
   compiles** with the pinned toolchain (Rust 1.99.0, edition 2024, see
   `code/rust/rust-toolchain.toml`), included with `{{#include}}` (section 4).
   A fragment that is not compiled (pseudo-code, a partial signature, unstable
   syntax) uses the fence ```` ```rust,ignore ```` and the text makes clear it
   is not compiled.
2. **Every Rust program that must be rejected is a file in
   `code/rust/compile_fail/`** and the diagnostics shown in the book are
   included from its `.stderr` snapshot, which `tools/run_examples.py --bless`
   captures from the real compiler.
3. **Every Rust output shown is included from `code/rust/output/<example>.txt`**,
   which `tools/run_examples.py --bless` captures from a real run.
4. **Every Lean snippet comes from a file in `code/lean/Book/` that builds with
   no messages at all** (no warnings, no `sorry`, no unguarded `#eval`). A Lean
   fragment that is not compiled (pseudo-code, a sketch of a definition you are
   about to build) uses ```` ```lean,ignore ````.
5. **Every Lean output shown is checked by Lean**: wrap the command in
   `#guard_msgs in` with the expected output in the doc comment above it, and
   include the whole block in the book. The same mechanism shows expected
   *errors*: `/-- error: ... -/ #guard_msgs in def bad ...`. Copy the message
   text from a real run (run once without the doc comment and read the error);
   never type it from memory.
6. **Verify every API, tactic and error message against the installed
   toolchains**, not against memory. Lean 4 and its standard library change
   quickly and much of what is online describes older versions (or Lean 3). The
   Lean sources of the installed toolchain are in
   `~/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/` (`Init/`, `Std/`),
   and Mathlib's are in `code/lean/.lake/packages/mathlib/Mathlib/`; they are
   the reference. For Rust, the standard library docs for 1.99 and
   `rustc --explain E0xxx` are the reference.
7. **Citations and history.** Cite only works you are sure of (author, title and
   year of the classics: Gentzen, Church, Curry, Howard, Martin-Löf, Girard,
   Reynolds, Wadler, Milner, Damas, Tofte and Talpin, Pierce's *TAPL*, Harper's
   *PFPL*, Jung et al.'s RustBelt). Do not invent page numbers, venues or URLs.
   When describing the status of ongoing work (Polonius, linear types for Rust,
   verification tools), say what it is and that the reader should check its
   current status; do not claim a release status you have not verified.
8. If something cannot be made to work, simplify the example or explain the
   limitation honestly. Never paper over it, never use `sorry`, never use
   `native_decide` (it trusts the compiler) unless the point of the section is
   to discuss it.

## 3. Where things go

```
book/src/NN-slug.md                       chapter sources (file names from OUTLINE.md)
book/diagrams/chNN-*.dot                  Graphviz sources of the diagrams
book/images/chNN-*.svg                    rendered diagrams (generated from .dot)
code/rust/examples/chNN_*.rs              single-file Rust examples (package book-examples)
code/rust/crates/<crate>/                 larger Rust programs (one crate per toy language)
code/rust/crates/<crate>/examples/chNN_*.rs  examples that use that crate
code/rust/compile_fail/chNN_*.rs          programs that must be rejected
code/rust/compile_fail/chNN_*.stderr      their diagnostics (generated, --bless)
code/rust/output/chNN_*.txt               example outputs (generated, --bless)
code/lean/Book/ChNN/*.lean                Lean files (module Book.ChNN.Name)
```

`book/chapters/`, `book/Types-Proofs-and-Ownership.pdf`, the `.txt` and
`.stderr` snapshots and the README's table of contents are generated: edit the
sources and rebuild them (see the README).

### Rust

- The workspace (`code/rust/Cargo.toml`) has **no external dependencies**. Use
  the standard library only. If you need randomness (property tests), write a
  tiny seeded PRNG (xorshift or SplitMix64) in the crate.
- The crates in `code/rust/crates/` already exist (see OUTLINE.md for which
  chapter owns which crate). Do not add, rename or remove crates.
- Code follows `code/rust/rustfmt.toml` (`max_width = 88`, so that lines fit on
  a printed page). Format your files with
  `rustfmt --edition 2024 <files>` (run from `code/rust`).
- Zero compiler warnings. Zero clippy-style cleverness: readability first.
- `cargo test -p <crate>` must pass for every crate; put unit tests next to the
  code (`#[cfg(test)] mod tests`).

### Lean

- The Lake project (`code/lean`) depends on **Mathlib** (pinned to the release
  that matches the toolchain, `v4.34.1`). Use it wherever it makes the material
  clearer: the `ℕ`/`ℤ` notation, `ring`, `linarith`, `norm_num`, `positivity`,
  `aesop`, `Finset` and `Fintype`, `Function.Injective`, `Equiv`, `Set`, the
  `CategoryTheory` library. Build things **from scratch** where constructing the
  definition *is* the lesson (the toy languages and their typing rules, the
  `Category` class of Chapter 16, the functor and monad classes with laws), and
  then show the corresponding Mathlib definition in a short section ("In
  Mathlib") so that the reader can continue with the real library.
- **Import only what you use** (`import Mathlib.Tactic.Ring`,
  `import Mathlib.Data.Fintype.Card`, `import Mathlib.CategoryTheory.Functor.Basic`),
  never the whole of `Mathlib`: every import is loaded each time a file is
  checked, and smaller imports keep checking fast. Find the module that defines a
  name by searching `.lake/packages/mathlib/Mathlib/` (for example
  `grep -rn "theorem Nat.succ_le_iff" .lake/packages/mathlib/Mathlib`).
- Mathlib changes quickly, and much of what is online (and in memory) describes
  older versions: **check every Mathlib name, notation and import path against
  the sources in `code/lean/.lake/packages/mathlib/`** by compiling. Never guess.
- One directory per chapter: `code/lean/Book/Ch05/Kripke.lean` is module
  `Book.Ch05.Kripke`. Everything in a file lives inside `namespace Ch05` (or a
  sub-namespace such as `Ch05.Kripke`), so that names never clash across
  chapters. Notations and instances that could leak into other chapters are
  `scoped` or `local`. Be careful with names that Mathlib already uses at the
  top level (`Category`, `Functor`, `Monad`, `Iso`...): inside your namespace they
  shadow Mathlib's, which is fine, but say so in the text, and refer to Mathlib's
  version with its full name (`CategoryTheory.Category`).
- A file may import Mathlib, files of **its own chapter**, and
  `Book.Ch16.Category` (the book's own category-theory core, shared by Part IV,
  which must not be modified except by adding anchors). Any other reuse across
  chapters is done by redefining what is needed, with a sentence in the text such
  as "we redefine the `Ty` type of Chapter 8 here".
- Check a single file quickly with `lake env lean Book/Ch05/Kripke.lean` (run in
  `code/lean`); it prints every message. Build a chapter's modules (needed when
  one file imports another) with `lake build Book.Ch05.Kripke`.
- File header: a module doc comment saying what the file demonstrates.

```lean
/-!
# Chapter 5 · Kripke semantics

Worlds, forcing and a two-world countermodel to the law of excluded middle.
-/

namespace Ch05
...
end Ch05
```

- **No messages.** `lake build` must print no `info:`, `warning:` or `error:`
  line for the book's files. Wrap every `#eval`, `#check`, `#print` and
  `#reduce` the book shows in `#guard_msgs in`; delete the ones it does not show.
- Prefer readable proofs. Use tactic proofs when they explain the reasoning
  (`intro`, `cases`, `induction`, `simp`, `omega`, `exact`), term proofs when
  they *are* the explanation (Curry–Howard chapters). Comment the steps of every
  proof the book shows until the reader has seen that tactic several times.
  Automation (`simp`, `omega`, `decide`, `grind`) is welcome once it has been
  introduced; say what it does the first time it appears in a chapter.
- Mathlib's identity-morphism notation `𝟙` is fine to use; the PDF template
  renders it with a math font.

## 4. Markdown format

The book is built from `book/src/*.md` into per-chapter Markdown and PDF files
plus a full-book PDF (pandoc → Typst). Write **GitHub-flavored Markdown** only.

### Chapter skeleton

```markdown
# The Curry–Howard Correspondence          <- H1 = title only; NO chapter number

Opening: 1–3 paragraphs of motivation.

**In this chapter you will learn:**       <- bold line + 4–7 bullets
- ...

## First major section                    <- H2 for sections, H3 for subsections
...
## Putting it together: <name>            <- walkthrough of a complete example
...
## Common confusions                       <- optional but encouraged
## Summary                                 <- bullet list of key takeaways
## Exercises                               <- 4–6 numbered exercises, each with a
                                              "*Hint:* ..." line; mix Rust, Lean
                                              and pen-and-paper exercises
```

The build adds "Chapter N" automatically — do not number headings. Refer to other
chapters as "Chapter 7", to sections by name. Use H2/H3/H4 only (no H5+).

**Length:** roughly 5,000–8,000 words of prose per chapter, plus code. Depth beats
breadth, but the topics listed in OUTLINE.md for the chapter must be covered.

### Including code

Mark regions in source files with anchor comments, `// ANCHOR: name` /
`// ANCHOR_END: name` in Rust and `-- ANCHOR: name` / `-- ANCHOR_END: name` in
Lean:

```lean
-- ANCHOR: and_swap
theorem and_swap (p q : Prop) : p ∧ q → q ∧ p :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩
-- ANCHOR_END: and_swap
```

and include them with a path **relative to the Markdown file**:

````markdown
```lean
{{#include ../../code/lean/Book/Ch10/Dictionary.lean:and_swap}}
```

```rust
{{#include ../../code/rust/examples/ch10_proofs_as_programs.rs:and_swap}}
```

```text
{{#include ../../code/rust/output/ch10_proofs_as_programs.txt}}
```

```text
{{#include ../../code/rust/compile_fail/ch10_contraction.stderr}}
```
````

- `{{#include path}}` includes a whole file; `{{#include path:10:20}}` lines 10–20
  (avoid line ranges for source files: they silently go stale; for an output
  snapshot that is long, a range is acceptable).
- Anchor lines and the `// harness:` line are stripped; the region is dedented.
- Anchors may nest/overlap; names must be unique within a file.
- Mention the file a snippet comes from in the prose the first time
  (e.g. "the full program is in `code/rust/examples/ch10_proofs_as_programs.rs`").
- Check the includes with `python3 tools/build_book.py check book/src/NN-*.md`.

### Mathematics

Mathematics is written in TeX between dollar signs and must render both on
GitHub (MathJax) and in the PDF (pandoc converts it to Typst math).

- Inline: `$\Gamma \vdash e : \tau$`. Display: `$$` on its own line before and
  after, with a blank line around the block.
- **Inference rules** are fractions, premises separated by `\qquad`, the rule
  name after `\;` in `\textsf{}`:

```markdown
$$
\dfrac{\Gamma \vdash f : \sigma \to \tau \qquad \Gamma \vdash a : \sigma}{\Gamma \vdash f\,a : \tau}\;\textsf{T-App}
$$
```

  Derivation trees nest `\dfrac`. Keep them small enough to fit the page width
  (about four premises side by side); split bigger derivations into named
  sub-derivations.
- Rule names in prose: `T-App` in plain text the first time, then **T-App** is
  not needed; write "rule T-App".
- Supported and checked: `\vdash \to \Rightarrow \Leftarrow \forall \exists
  \lambda \Lambda \Gamma \Delta \tau \sigma \alpha \beta \otimes \oplus
  \multimap \top \bot \neg \land \lor \leftrightarrow \cong \circ \times
  \uplus \mapsto \llbracket \rrbracket \mathbb{N} \mathcal{C} \mathsf{} \mathtt{}
  \mathrm{} \operatorname{} \text{}`. Use `\mathbin{\&}` for the additive
  conjunction "with" and the Unicode character `⅋` for "par".
- **Not supported** (the build check rejects them): `\textsc`, `\parr`,
  `\inferrule`, `prooftree` environments. Avoid `\begin{array}` and `aligned`
  environments unless you have checked the PDF output.
- Use math where it genuinely helps; a sentence is often clearer than a formula.

### Other blocks

- Fences: `rust`, `rust,ignore`, `lean`, `lean,ignore`, `text` (program output
  and diagnostics), `sh` (commands the reader types), `toml`.
- Callouts (GitHub alerts), used sparingly — at most ~1 per 800 words:
  `> [!NOTE]`, `> [!TIP]`, `> [!IMPORTANT]`, `> [!WARNING]`, `> [!CAUTION]`.
- Figures: an image alone in its paragraph becomes a captioned figure:
  `![The Curry–Howard–Lambek triangle.](../images/ch19-trinity.svg)`
  The alt text **is** the caption: write a full sentence.
- Tables: pipe tables, ≤ 5 columns, short cells. Tables are the best format for
  dictionaries ("logic / type theory / Rust / Lean").
- Links: only to URLs you know exist (https://lean-lang.org,
  https://doc.rust-lang.org, https://www.rust-lang.org). Do not invent deep links.
  Refer to API items in `code` formatting.

## 5. Code conventions

### Rust examples

- File: `code/rust/examples/chNN_<slug>.rs` (or
  `code/rust/crates/<crate>/examples/chNN_<slug>.rs` when it uses a crate).
- Line 1 is the harness directive, then an inner doc comment:

```rust
// harness: run
//! Proofs as programs: the propositional tautologies of Chapter 10 as generic
//! Rust functions.
//!
//! Run with: `cargo run --example ch10_proofs_as_programs`
```

- **Harness directive grammar** (used by `tools/run_examples.py`):
  - `// harness: run [timeout=SECONDS]` — must exit with code 0 by itself; its
    standard output is compared with `code/rust/output/<name>.txt`.
  - `// harness: build-only` — only compiled (rare).
- Examples are deterministic (no unseeded randomness, no timing in the output,
  no `HashMap` iteration order: use `BTreeMap` or sort), finish within a few
  seconds, and print concise output (ideally ≤ 40 lines) meant to be shown in
  the book. Use `assert!`/`assert_eq!` generously: an example is also a test.
- Readability over cleverness: descriptive names, comments explaining *why*.
  Keep examples focused (~60–300 lines).

### Compile-fail programs

- File: `code/rust/compile_fail/chNN_<slug>.rs`, compiled on its own as a
  library (`rustc --edition 2024 --crate-type lib -A warnings`), so it needs no
  `main` and cannot use the crates.
- Line 1 lists the error codes it must produce:

```rust
// harness: compile-fail E0382
//! Contraction is not free: a non-Copy value cannot be used twice.
```

- A diagnostic without an error code (for example "lifetime may not live long
  enough", or a lint made an error with `#![deny(unused_must_use)]`) is checked by
  a quoted text instead: `// harness: compile-fail "may not live long enough"`.
- Keep them tiny (5–25 lines) so the diagnostic is short and to the point. The
  book includes the `.stderr` snapshot in a `text` fence and explains how the
  error relates to the theory.

### Lean files

- See section 3. Keep files focused (~50–400 lines); split big developments into
  several files of the same chapter (`Syntax.lean`, `Typing.lean`,
  `Safety.lean`) that import each other.

## 6. Diagrams

Use Graphviz for concept diagrams (1–3 per chapter where they genuinely help:
derivation shapes, lattices of logics, categories and commutative diagrams,
compiler pipelines, control-flow graphs). The source goes in
`book/diagrams/chNN-name.dot`; `python3 tools/build_book.py diagrams` renders it
to `book/images/chNN-name.svg`.

Shared visual language (keep it consistent across the book):

```dot
digraph G {
  graph [bgcolor="white", fontname="Helvetica", fontsize=11, pad=0.2, nodesep=0.35, ranksep=0.45];
  node  [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=11,
         color="#475569", fillcolor="#f1f5f9", penwidth=1.2, margin="0.12,0.06"];
  edge  [color="#475569", fontname="Helvetica", fontsize=10, arrowsize=0.7];
  // Logic / proposition       fillcolor="#dbeafe" color="#1d4ed8"
  // Type / object             fillcolor="#dcfce7" color="#15803d"
  // Term / program / morphism fillcolor="#ffedd5" color="#c2410c"
  // Rust-specific             fillcolor="#fee2e2" color="#b91c1c"
  // Lean-specific             fillcolor="#f3e8ff" color="#7e22ce"
  // Neutral / other           fillcolor="#f1f5f9" color="#475569"
}
```

Keep diagrams small (≤ ~15 nodes), labels short. For commutative diagrams, use
`rank=same` subgraphs to put the corners of a square on two rows, plain-text
node shapes (`shape=plaintext`) and edge labels for the morphisms. Use Unicode in
labels (`→`, `×`, `⊗`, `⊢`, `Γ`, `τ`) rather than TeX.

Write `fontname="Helvetica"` as in the template: the build replaces every font
with STIX Two Math when it renders the diagrams, because the PDF's SVG renderer
uses a single font per label and shows empty boxes for the whole label when that
font lacks one of its symbols. STIX Two Math has Latin, Greek and the
mathematical symbols the book uses.

## 7. Checklist

1. Every Rust example: zero warnings; runs according to its harness directive;
   snapshot blessed and reviewed (`python3 tools/run_examples.py --only chNN`).
2. Every compile-fail program fails with the listed codes; `.stderr` blessed and
   reviewed.
3. `lake build` prints no messages for the chapter's Lean files
   (`python3 tools/run_examples.py --lean --only chNN`).
4. `cargo test -p <crate>` passes for the chapter's crates.
5. `python3 tools/build_book.py check book/src/NN-*.md` passes.
6. The chapter follows the skeleton (learning goals, sections, walkthrough,
   summary, exercises with hints) and the length target, and covers every topic
   OUTLINE.md lists for it.
7. The generated files are rebuilt: `python3 tools/build_book.py all`.
