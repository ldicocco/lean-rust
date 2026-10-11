# Types, Proofs and Ownership — Course Outline

**Full title:** *Types, Proofs and Ownership — Type Theory, Logic and Category
Theory through Rust and Lean 4*

**Reader.** A programmer who uses Rust actively (ownership, borrowing, traits,
generics, closures, iterators, `Result`, Cargo) without being an expert, and who
knows very little Lean, type theory, logic or category theory, but has a very
active interest in them. They want to *understand*: real definitions, real rules,
real proofs, and how all of it shows up in the Rust they write every day.

**Versions.** Rust 1.99.0 (edition 2024, standard library only). Lean 4.34.1
with Mathlib `v4.34.1`.

**Using Mathlib.** Mathlib is used wherever it makes the material clearer
(`ℕ`, `ring`, `linarith`, `norm_num`, `Finset`/`Fintype`, `Equiv`, `Set`,
`CategoryTheory`), and the reader is introduced to it gently (Chapter 2). Things
are built **from scratch** where constructing the definition is the lesson: the
toy languages and their rules, the book's own `Category` class (Chapter 16), the
functor and monad classes with laws. Each such construction is followed by a
short "In Mathlib" section that shows the library's version, so that the reader
can continue with the real thing.

**Method.** Every idea appears in three forms: the mathematics (rules,
definitions, diagrams), Rust (where the idea lives in a production language, and
where Rust deviates from the clean theory) and Lean (the idea stated precisely
and checked by a machine). Rust implements; Lean proves.

**Threads that run through the book.**

- *The question.* Chapter 1 asks: "Is it true that Rust's ownership and lifetimes
  are based on affine types?" Parts V and VI build the apparatus to answer it;
  Chapter 33 gives the verdict (half true: ownership and moves are affine;
  borrowing and lifetimes are a region-and-permission system).
- *Three readings of a type*: a classification of values (the programmer), a
  proposition (the logician), an object (the category theorist).
- *A sequence of toy languages*, each implemented in Rust and formalized in Lean:
  `Arith` (Ch. 3), propositional proofs (Ch. 4), the untyped λ-calculus (Ch. 7),
  the simply typed λ-calculus (Ch. 8–9), mini-ML with type inference (Ch. 13),
  linear sequents (Ch. 21), the affine λ-calculus (Ch. 22–23), a core calculus of
  borrowing (Ch. 28), a miniature MIR (Ch. 29).

**Examples domain.** Language tools, protocols and resources (network
connections, files, locks, payment and order workflows, lab instruments), data
structures, units and matrices. Never games.

Chapter numbers below are final — refer to other chapters as "Chapter N".

**Ownership of shared code.** Each crate in `code/rust/crates/` belongs to the
chapter listed here; other chapters may describe it but do not modify it. The
Lean module `Book.Ch16.Category` is shared by Part IV.

| Crate | Chapter(s) |
|---|---|
| `arith` | 3 |
| `natded` | 4 |
| `lambda` | 7 |
| `stlc` | 8 |
| `safety` | 9 |
| `hm` | 13 |
| `linlogic` | 21 |
| `affine` | 22, 23 |
| `borrowck` | 28 |
| `mini-nll` | 29 |

---

## Front matter

- **Preface** (`00-preface.md`) — who the course is for, why Rust and Lean
  together, how the course is organized, conventions (how includes, outputs,
  compile-fail diagnostics and `#guard_msgs` work), how to run the code.

## Part I — Foundations

### Chapter 1 · Two Languages, One Idea (`01-two-languages.md`)
What a type theory is: syntax, judgments, rules, computation. The three readings
of a type. Why Rust (a production language with an unusually rich type system:
algebraic data types, parametric and ad-hoc polymorphism, existentials, an
affine core, regions) and Lean (a dependently typed functional language that is
also a proof assistant) make a good pair. The question of the book. A first look
at both languages: the same function in Rust and Lean, then a *theorem* about it
in Lean. `#eval`, `#check`, `#guard_msgs` and `#print axioms`. A first
compile-time rejection in each language. Map of the book.
Code: Rust `examples/ch01_first_types.rs`; compile-fail
`ch01_if_branches.rs` (E0308); Lean `Book/Ch01/FirstSteps.lean`.

### Chapter 2 · Lean 4 for Rust Programmers (`02-lean-for-rust-programmers.md`)
Lean as a programming language, from a Rust programmer's point of view.
`def`, signatures, `fun`, implicit arguments `{α : Type}`, pattern-matching
definitions; `structure` vs `struct`; `inductive` vs `enum`; `match`;
`Option`, `Except` (vs `Result`), `List` and `Array` (persistent values vs `Vec`);
`deriving Repr, BEq, DecidableEq` vs `#[derive]`; namespaces and dot notation vs
modules and `impl` blocks; type classes vs traits (`class`/`instance` vs
`trait`/`impl`): `ToString`, `BEq`, `Hashable`, `Inhabited`; `do` notation, `IO`,
`let mut` and `for` loops inside `do` (sugar for pure code); totality: the
termination checker, structural recursion, `partial`, `termination_by` (brief),
vs Rust's unrestricted recursion and `loop`; immutability and Lean's
reference-counted in-place updates (preview of Chapter 24); `theorem` and
`example`; first tactics (`rfl`, `decide`, `simp`, `omega`, `induction`); reading
the infoview and error messages; `sorry` and why the book never uses it.
**Mathlib**: what it is (the community's library of mathematics, also a library
of tactics), how a Lake project depends on it (like a Cargo dependency, with a
prebuilt cache), importing only what you use, the notation it adds (`ℕ`, `ℤ`),
the tactics the book uses most (`ring`, `linarith`, `norm_num`, `positivity`),
finding lemmas (`exact?`, `apply?`, naming conventions such as
`Nat.add_comm`, `mul_le_mul`), and how core Lean and Mathlib divide the work. A
Rust ↔ Lean syntax table.
Code: Rust `examples/ch02_orders.rs` (an order book: structs, enums, `Result`,
`BTreeMap`, iterators); Lean `Book/Ch02/Basics.lean`, `Book/Ch02/Orders.lean`
(the same program in Lean, side by side), `Book/Ch02/FirstProofs.lean`
(properties of the order book proved).

### Chapter 3 · Judgments, Rules and Derivations (`03-judgments-rules.md`)
Abstract syntax (trees, BNF). Judgments ($\Gamma \vdash e : \tau$), inference
rules (premises, conclusion, axioms), derivations as trees. The language `Arith`:
natural and boolean literals, `+`, `==` or `<=`, `if`, `let`, variables. Rust's
expressions as instances: everything is an expression, blocks, `if` and rule
T-If (both branches share one type), unit, the never type `!` and its coercion,
`Infallible`. Type safety stated informally (progress, preservation; "well-typed
programs don't go wrong") and what "wrong" means. Checking vs synthesis vs
inference (preview of Chapters 8 and 13). Structural vs nominal types.
Rust: the `arith` crate (AST, type checker producing derivation trees, evaluator,
tests). Lean: syntax as an `inductive`, the typing judgment as an inductive
predicate `HasType : Ctx → Expr → Ty → Prop`, derivations as proof terms (by hand,
then with `constructor`/`repeat`), the type checker as a function, and the
first real theorem: **the checker is sound** (`check Γ e = some τ → HasType Γ e τ`),
plus uniqueness of types.
Code: crate `arith` + `crates/arith/examples/ch03_arith.rs` (checks sample
programs, prints derivation trees as indented text); compile-fail
`ch03_never_coerces.rs` or similar if it teaches something (optional); Lean
`Book/Ch03/Arith.lean`, `Book/Ch03/Soundness.lean`.

### Chapter 4 · Natural Deduction (`04-natural-deduction.md`)
Propositions vs judgments ("$A$ true"). Introduction and elimination rules for
$\land$, $\to$, $\lor$, $\top$, $\bot$, and $\neg A$ as $A \to \bot$.
Hypothetical judgments and discharging assumptions; tree notation vs sequent
notation ($\Gamma \vdash A$). Harmony: local soundness (detours can be removed)
and local completeness (expansions), the preview of $\beta$ and $\eta$. Prior's
`tonk` and why harmony is a real filter. Why $\lor$E and $\bot$E look strange.
Normalization, the subformula property, consistency. Sequent calculus and cut
elimination (overview). Lean: propositions live in `Prop`, proofs as terms and as
tactic scripts (`intro`, `exact`, `apply`, `constructor`, `cases`/`rcases`,
`obtain`, `left`/`right`, `exfalso`, `contradiction`), `#print` a tactic proof's
term. A deep embedding: formulas, an inductive derivability relation
`Proves : List Formula → Formula → Prop`, and **soundness with respect to truth
tables** proved by induction on derivations. Rust: the `natded` crate, a proof
checker for natural-deduction proof trees with good error messages, plus a
truth-table evaluator; adding `tonk` makes the checker accept a proof of $\bot$.
Code: crate `natded` + `crates/natded/examples/ch04_proof_checker.rs`; Lean
`Book/Ch04/Tactics.lean` (shallow), `Book/Ch04/Deep.lean` (deep embedding +
soundness).

### Chapter 5 · Intuitionism and the Meaning of Proof (`05-intuitionism.md`)
Brouwer and the BHK interpretation (a proof of $A \lor B$ is a proof of one of
them, *with the information which*; a proof of $A \to B$ is a method). What fails
constructively: excluded middle, double-negation elimination, Peirce's law, one
De Morgan law; what you gain: the disjunction and existence properties (proofs
carry witnesses). Classical logic is not "wrong": the double-negation translation,
$\neg\neg(p \lor \neg p)$ is provable. Truth, falsity and negation;
$\neg A = A \to \bot$. Kripke semantics (worlds, accessibility, monotone forcing)
and a two-world countermodel to excluded middle. Heyting algebras (finite
examples, the three-element chain) and why they validate intuitionistic but not
classical logic; the categorical reading (preview of Chapter 19). Lean:
`Classical.em`, `Classical.byContradiction`, `Decidable` and why `if` on a `Prop`
needs it, `#print axioms` to see which proofs are classical, constructive proof
of $\neg\neg(p \lor \neg p)$. Rust: negation as `fn(A) -> Void` with an empty
enum, `Infallible`, the never type; an exhaustive Kripke countermodel search.
Code: `examples/ch05_kripke.rs` (searches small Kripke frames for countermodels
of LEM, DNE, Peirce, and confirms a few intuitionistic tautologies);
`examples/ch05_negation.rs` (empty types and negation as functions); Lean
`Book/Ch05/Constructive.lean`, `Book/Ch05/Kripke.lean` (forcing, a two-world
countermodel to LEM checked by `decide`), `Book/Ch05/Heyting.lean` (a
`HeytingAlgebra` class built from scratch, the three-element instance, which
laws hold; then Mathlib's `HeytingAlgebra`, of which `Prop` is an instance).

### Chapter 6 · The Structural Rules (`06-structural-rules.md`)
Exchange, weakening and contraction as rules about contexts. Admissible vs
derivable vs built-in (contexts as lists, multisets or sets). The design
decision: which rules a logic keeps determines what an assumption *is*. A first
glance at Rust: unused variables and `drop` (weakening, with an effect),
moves and E0382 (no contraction), `Copy` types (contraction restored),
evaluation order and exchange. The resource reading of assumptions, preparing
Part V. Lean: contexts as lists; weakening, exchange and contraction proved
**admissible** for the natural-deduction system of Chapter 4 (redefined here) by
induction on derivations; counting how often an assumption is used.
Code: `examples/ch06_structural.rs` (the three rules as Rust programs);
compile-fail `ch06_use_after_move.rs` (E0382), `ch06_move_in_loop.rs` (E0382);
Lean `Book/Ch06/Structural.lean`.

## Part II — Programs as Proofs

### Chapter 7 · The Lambda Calculus (`07-lambda-calculus.md`)
The untyped λ-calculus: syntax, free and bound variables, α-equivalence,
capture-avoiding substitution, β-reduction, reduction strategies (normal order,
call-by-value, call-by-name), normal forms, confluence (Church–Rosser, stated),
divergence ($\Omega$), fixed-point combinators (Y, Z), Church encodings
(booleans, numerals, pairs, arithmetic). De Bruijn indices: shifting and
substitution. Rust: the `lambda` crate (named terms with capture-avoiding
substitution, conversion to de Bruijn, normal-order and call-by-value reducers
with step limits, a pretty printer), Church arithmetic computed, $\Omega$ running
out of fuel. Rust closures as λ-terms (but typed: why `|x| x(x)` is rejected,
preview of Chapter 8). Lean: de Bruijn terms as an inductive, `shift` and `subst`,
the one-step β relation as an inductive predicate, a fuel-based total normalizer
vs `partial def`, and why Lean rejects a general normalizer without `partial`
(show the termination error with `#guard_msgs`); small proofs (a specific term
reduces to another; $\Omega$ steps to itself).
Code: crate `lambda` + `crates/lambda/examples/ch07_church.rs`; compile-fail
`ch07_self_application.rs` (E0282 or E0308/E0644: check); Lean
`Book/Ch07/Untyped.lean`.

### Chapter 8 · The Simply Typed Lambda Calculus and Closures (`08-stlc-closures.md`)
STLC with unit, booleans, naturals, pairs and sums; introduction and elimination
rules; $\beta$ and $\eta$; strong normalization (stated) and why $\lambda x.\,x\,x$
has no type; termination vs Rust's Turing completeness. Functions in Rust: `fn`
items, function pointers, closures with unique anonymous types, `impl Fn`,
`dyn Fn`, capture modes (by reference, by mutable reference, by value, `move`),
the `Fn`/`FnMut`/`FnOnce` hierarchy as "how many times may a resource be used"
(first glimpse of Part V), the cost of currying in Rust. Bidirectional type
checking (synthesis and checking modes, annotations, why λ checks but does not
synthesize). Rust: the `stlc` crate, a bidirectional checker plus an
environment-based evaluator with closures. Lean: **intrinsically typed** terms
(`Term : List Ty → Ty → Type`, variables as typed membership proofs), a
denotational evaluator into Lean types (`Ty.denote`) that is total and safe by
construction; extrinsic vs intrinsic typing.
Code: crate `stlc` + `crates/stlc/examples/ch08_stlc.rs`;
`examples/ch08_closures.rs` (capture modes, the three traits, currying);
compile-fail `ch08_fnonce_twice.rs` (E0382), `ch08_fn_mutates.rs` (E0594 or
E0596: check); Lean `Book/Ch08/Intrinsic.lean`.

### Chapter 9 · Type Safety, Proved (`09-type-safety.md`)
Small-step operational semantics as an inductive relation; values and stuck
terms; canonical forms; progress; weakening and substitution lemmas;
preservation; type safety (multi-step) as a corollary; determinism of
evaluation. All of it for STLC with booleans and naturals, extrinsically typed
with de Bruijn indices, **fully mechanized in Lean** and walked through lemma by
lemma (the chapter's centerpiece). Rust: the `safety` crate, a small-step
evaluator and a property-based test harness (own seeded PRNG, random generator
of well-typed terms) that checks progress and preservation on thousands of
terms; tests vs proofs. What "going wrong" means for Rust (undefined behavior vs
panics), and what the type system does not promise (termination, absence of
panics, leaks, deadlocks).
Code: crate `safety` + `crates/safety/examples/ch09_fuzz_safety.rs`; Lean
`Book/Ch09/Syntax.lean`, `Book/Ch09/Semantics.lean`, `Book/Ch09/Typing.lean`,
`Book/Ch09/Safety.lean`.

### Chapter 10 · The Curry–Howard Correspondence (`10-curry-howard.md`)
The dictionary: implication ↔ function, conjunction ↔ product, disjunction ↔ sum,
true ↔ unit, false ↔ empty type, negation ↔ function into the empty type,
universal quantification ↔ dependent function / generics, existential ↔
dependent pair / existential type. Normalization is computation: proof detours
are β-redexes. Rust: tautologies as generic functions (`fn and_comm<A, B>`,
`Either`, `Void`), what Rust cannot express (quantifying over values), and why
Rust is **inconsistent as a logic** (`loop {}`, `panic!`, `todo!()` inhabit every
type) while Lean is not (totality, `partial` requires `Inhabited`, `sorry` is
tracked by `#print axioms`). Contraction: where Rust makes the logic honest
($A \to A \land A$ needs `Clone`/`Copy`, foreshadowing Part V). Lean: `Prop` vs
`Type`, proof irrelevance, impredicativity of `Prop`, `Exists` vs `Sigma` vs
`Subtype`, why the witness of an `Exists` cannot be extracted into data (the
elimination restriction), `theorem` vs `def`, `Nat.le` as an inductive family,
`#print` of the term behind a tactic proof.
Code: `examples/ch10_proofs_as_programs.rs`; compile-fail
`ch10_contraction.rs` (E0382); Lean `Book/Ch10/Dictionary.lean`,
`Book/Ch10/PropVsType.lean`.

### Chapter 11 · Algebraic Data Types and the Algebra of Types (`11-algebraic-data-types.md`)
The type formers product, sum, unit, empty and function; cardinalities
($|A \times B| = |A|\,|B|$, $|A + B| = |A| + |B|$, $|A \to B| = |B|^{|A|}$);
isomorphisms as "equalities" of types ($A \times 1 \cong A$,
$A \times (B + C) \cong A \times B + A \times C$, currying, $A^{B+C} \cong A^B \times A^C$),
**proved in Lean** with an `Iso` structure (round-trip proofs). Recursive types as
fixed points ($\mathrm{List}\,A = 1 + A \times \mathrm{List}\,A$), `Box` and
`Sized` in Rust (E0072), positivity in Lean (why
`inductive Bad | mk : (Bad → Nat) → Bad` is rejected: show the error). Rust:
`Option`, `Result`, zero-sized types, uninhabited types and `match x {}`, niche
optimization (`size_of::<Option<&T>>()`, `Option<Box<T>>`, `Option<NonZeroU32>`),
exhaustiveness as the elimination rule. Lean: our own `Iso` first, then Mathlib's
`Equiv` (`α ≃ β`) and its library of isomorphisms; cardinalities with Mathlib's
`Fintype.card` (`Fintype.card (α × β) = ...` by `simp`), checked on concrete
types. Bonus: derivatives of types and zippers.
Code: `examples/ch11_type_algebra.rs` (isomorphisms as function pairs with
round-trip assertions, a `size_of` table); compile-fail
`ch11_recursive_without_box.rs` (E0072); Lean `Book/Ch11/Iso.lean`,
`Book/Ch11/Cardinality.lean`, `Book/Ch11/Positivity.lean`.

## Part III — Abstraction

### Chapter 12 · Parametric Polymorphism (`12-parametric-polymorphism.md`)
System F: type abstraction $\Lambda\alpha$, type application, $\forall\alpha.\,\tau$,
typing rules; Church encodings in System F; impredicativity. Rust generics as
$\forall$ with monomorphization (vs erasure and dictionary passing: code size,
speed, compile time), the turbofish as explicit type application, trait bounds
as bounded quantification (preview of Chapter 14), Rust's rank-1 restriction for
types, rank-2 via a trait with a generic method, higher-ranked trait bounds
`for<'a>` over lifetimes. Lean: implicit arguments and `@`, universe polymorphism
(`Type u`, `Sort u`), predicativity (`Type u : Type (u+1)`) and why System F's
impredicativity survives only in `Prop`; Church numerals as
`(α : Type) → (α → α) → α → α` living in `Type 1`; rank-n functions are ordinary
dependent functions. A System F type checker in Lean or Rust (optional, small).
Code: `examples/ch12_generics.rs` (monomorphization made visible, turbofish,
rank-2 via traits, HRTB); compile-fail `ch12_rank2_closure.rs` (a closure
argument used at two types: E0308); Lean `Book/Ch12/Universes.lean`,
`Book/Ch12/Church.lean`.

### Chapter 13 · Type Inference (`13-type-inference.md`)
Why infer types; type variables and substitutions; unification (most general
unifiers, the occurs check); Hindley–Milner: let-polymorphism, generalization and
instantiation, algorithm W, principal types; limits of HM. Rust: the `hm` crate,
algorithm W for a mini-ML with readable error messages (the occurs check rejects
$\lambda x.\,x\,x$); Rust's own inference: local to function bodies, signatures
as boundaries, "type annotations needed" (E0282), integer literal defaulting,
closures are not generalized (E0308 when used at two types), `collect::<Vec<_>>`.
Lean's elaborator: metavariables, unification with dependent types (higher-order
unification is undecidable in general), `_` holes, "don't know how to synthesize
placeholder", type ascriptions `(e : τ)` and `show`. Lean: first-order
unification implemented with fuel and run with `#eval`; a proved property of
substitution (e.g. composition of substitutions).
Code: crate `hm` + `crates/hm/examples/ch13_infer.rs`; compile-fail
`ch13_annotations_needed.rs` (E0282), `ch13_closure_not_generic.rs` (E0308);
Lean `Book/Ch13/Unify.lean`, `Book/Ch13/Elaboration.lean`.

### Chapter 14 · Traits, Type Classes and Dictionary Passing (`14-traits-type-classes.md`)
Ad-hoc vs parametric polymorphism; type classes (Wadler and Blott) as constrained
polymorphism; elaboration into dictionary passing (a Rust generic function with
a trait bound rewritten to take an explicit struct of functions; how vtables
relate); coherence and the orphan rule (why instances must be globally unique;
E0117), blanket impls, overlap and specialization (unstable: mention only);
associated types vs type parameters (functional dependencies; Lean's `outParam`);
supertraits; default methods. **Laws**: Rust cannot state that `combine` is
associative, only test it; Lean classes can carry proof fields
(`LawfulMonoid`), instances must prove them. Lean: `class` is a `structure`,
instance resolution, `inferInstance`, local instances, priorities, default
methods, `Decidable` as a class, `Inhabited`.
Code: `examples/ch14_dictionary_passing.rs` (a `Monoid` trait and the same code
with explicit dictionaries; law tests on samples); compile-fail
`ch14_orphan.rs` (E0117); Lean `Book/Ch14/Monoid.lean`,
`Book/Ch14/Dictionaries.lean`.

### Chapter 15 · Existential Types and Dynamic Dispatch (`15-existential-types.md`)
$\exists\alpha.\,\tau$: pack and unpack rules; abstract data types have
existential type (Mitchell and Plotkin); modules and information hiding. Rust:
`impl Trait` in return position (an existential chosen by the callee, opaque to
the caller), `dyn Trait` as an existential package (data pointer + vtable), fat
pointers and `size_of`, dyn compatibility (object safety) and why (E0038),
`Box<dyn Any>` and downcasting (runtime type information breaks parametricity,
preview of Chapter 18). Encoding $\exists$ with $\forall$
($\exists\alpha.\,\tau \cong \forall\beta.\,(\forall\alpha.\,\tau \to \beta) \to \beta$)
in Rust (a visitor trait with a generic method) and in Lean. Lean: structures
with a type field (a counter ADT), the universe bump (it lives in `Type 1`),
Σ-types `(α : Type) × (α → String)`, `Exists` vs `Sigma` again.
Code: `examples/ch15_existentials.rs` (a counter ADT three ways: generics,
`impl Trait`, `dyn Trait`; the CPS encoding); compile-fail
`ch15_dyn_incompatible.rs` (E0038); Lean `Book/Ch15/Existential.lean`.

## Part IV — Categories

### Chapter 16 · Categories for Programmers (`16-categories.md`)
Categories: objects, morphisms, identities, composition, unit and associativity
laws. Examples: Lean types and functions; Rust types and functions (with the
caveats: side effects, panics, non-termination); preorders (≤ on numbers, and
later lifetimes ordered by "outlives"); monoids as one-object categories;
discrete categories; free categories of paths in a graph. Commutative diagrams.
Isomorphisms; monomorphisms and epimorphisms (injective and surjective
functions). Initial and terminal objects (empty type and unit), uniqueness up to
unique isomorphism. Products and coproducts by universal property, **proved in
Lean** for `Type` (pairs and `Sum`); duality and the opposite category. Lean: the
shared `Book.Ch16.Category` module (the book's own class with laws as fields,
`typeCategory`, `Iso`, `Op`), more instances (a preorder, a monoid) with proofs
by `funext`, `rfl`, `simp`; then **In Mathlib**: `CategoryTheory.Category`, its
notation (`⟶`, `≫` in diagrammatic order, `𝟙`), `Type u` as a category, and
`Limits` for products (shown, with a few small proofs). Rust: composition written
generically, laws checked on samples.
Code: `examples/ch16_categories.rs`; Lean `Book/Ch16/Category.lean` (shared core:
may add anchors, must not change existing declarations),
`Book/Ch16/Examples.lean`, `Book/Ch16/Universal.lean`.

### Chapter 17 · Functors and Higher-Kinded Types (`17-functors-hkt.md`)
Kinds: `Type`, `Type → Type`, `Type → Type → Type`; type constructors and partial
application. Functors between categories (on objects and on morphisms,
preserving identities and composition); endofunctors on types: `Option`, `Vec`,
`Result<_, E>`, `(E, _)`, `fn(E) -> _`; the functor laws. Rust has `map` methods
everywhere but no `Functor` trait: the missing higher-kinded types; workarounds
with generic associated types (a "family" trait) and their limits. Lean:
`Type → Type` is just a function type; core `Functor` and `LawfulFunctor`; our own
functor class with laws, instances proved for `Option`, `List` and a tree.
Contravariant functors (predicates, comparators), bifunctors (pairs, `Result`),
functions as profunctors (brief). Functors between general categories using
`Book.Ch16.Category` (e.g. monotone maps between preorders), then Mathlib's
`CategoryTheory.Functor` (`C ⥤ D`). Preview of variance (Chapter 27) as
functoriality.
Code: `examples/ch17_functors.rs` (law checks for `Option`/`Vec`/`Result`, a
GAT-based `Functor` trait); Lean `Book/Ch17/Functor.lean`,
`Book/Ch17/CatFunctor.lean`.

### Chapter 18 · Natural Transformations and Free Theorems (`18-natural-transformations.md`)
Natural transformations and naturality squares. Polymorphic functions are
natural transformations (`fn first<T>(v: Vec<T>) -> Option<T>`, `Option::into_iter`,
`reverse`). Parametricity (Reynolds) and free theorems (Wadler, "Theorems for
free!"): a function of type $\forall\alpha.\,\alpha \to \alpha$ is the identity; a
function $\forall\alpha.\,\mathrm{List}\,\alpha \to \mathrm{List}\,\alpha$ commutes
with `map`. Where Rust leaks parametricity: trait bounds, `size_of::<T>()`,
`TypeId`/`Any`, side effects and panics, (unstable) specialization. Lean: naturality
proved for concrete transformations (`List.head?`, `List.reverse`,
`Option.toList`), why the general free theorem is not provable *inside* Lean
(parametricity is a meta-theorem), composition of natural transformations. The
Yoneda lemma, gently: $\forall\beta.\,(\alpha \to \beta) \to F\,\beta \;\cong\; F\,\alpha$,
in Lean (proved for functors satisfying the laws) and as continuation-passing in
Rust; Mathlib's `NatTrans` and `yoneda` for orientation.
Code: `examples/ch18_naturality.rs` (naturality squares checked on samples;
breaking parametricity with `Any` and `size_of`); Lean `Book/Ch18/Natural.lean`,
`Book/Ch18/Yoneda.lean`.

### Chapter 19 · Cartesian Closed Categories (`19-cartesian-closed.md`)
Terminal objects and products in a category (recap), exponential objects
(`curry`, `eval`) and their universal property; cartesian closed categories.
Adjunctions introduced gently through currying:
$\mathrm{Hom}(A \times B, C) \cong \mathrm{Hom}(A, C^B)$. Lambek's correspondence:
the STLC and CCCs (types as objects, terms in context as morphisms, $\beta$/$\eta$ as
equations); interpreting the STLC in a CCC (a denotational semantics into
Lean's `Type`, with $\beta$ sound by `rfl`). Heyting algebras are thin CCCs (back
to Chapter 5). The Curry–Howard–Lambek triangle. Rust: the categorical combinators
(`curry`, `uncurry`, `eval`) and why Rust is **not cartesian** for non-`Copy`
types: the diagonal $A \to A \times A$ needs `Clone`, and `(A, B)` with moves is a
*monoidal* product; symmetric monoidal closed categories as the models of linear
logic (preview of Part V).
Code: `examples/ch19_ccc.rs`; compile-fail `ch19_diagonal.rs` (E0382); Lean
`Book/Ch19/CCC.lean` (imports `Book.Ch16.Category`; products, exponentials,
`CartesianClosed`, instance for `Type`, a Heyting algebra as a thin CCC),
`Book/Ch19/Semantics.lean` (STLC into a CCC); Mathlib's `CartesianClosed` for
orientation.

### Chapter 20 · Monads and Effects (`20-monads.md`)
Effects break "functions as morphisms"; Kleisli arrows $A \to M\,B$; monads as
(`M`, `pure`, `bind`) with three laws. `Option`, `Except`/`Result`, `List`
(nondeterminism), `State`, `Reader`, `Writer`. Rust: `?` as bind for `Option` and
`Result` (the `Try` trait is unstable: mention only), `and_then`, `flat_map`,
iterator adapters; async/await as a compiler-supported effect; why Rust has no
`Monad` trait (higher-kinded types, and ownership: `bind` for `Vec` needs `FnMut`,
for `Option` `FnOnce`). Lean: the `Monad` class, `do` notation and its desugaring,
`LawfulMonad`, our own monad class with laws proved for `Option` and `State`; the
Kleisli category (built with `Book.Ch16.Category`): monad laws are category laws;
`IO`; monad transformers (`StateT`, `ExceptT`) vs Rust's ad-hoc approach;
adjunctions give rise to monads (brief; Mathlib's `CategoryTheory.Adjunction`
and `CategoryTheory.Monad`).
Code: `examples/ch20_monads.rs` (chains with `?`, a `State` monad with closures,
`flat_map` as bind for lists); Lean `Book/Ch20/Monad.lean`,
`Book/Ch20/Kleisli.lean`, `Book/Ch20/State.lean`.

## Part V — Ownership as Logic

### Chapter 21 · Substructural Logics (`21-substructural-logics.md`)
Recap of the structural rules; the lattice of logics: ordinary (exchange,
weakening, contraction), affine (no contraction), relevant (no weakening), linear
(neither), ordered (no exchange either). Multiplicative vs additive connectives:
$A \otimes B$ (tensor) vs $A \mathbin{\&} B$ (with), $\oplus$, $⅋$; linear
implication $\multimap$; the resource reading (Girard's examples: a coin buys a
coffee *or* a tea, not both); context splitting ($\Gamma_1 \uplus \Gamma_2$) vs
sharing; full linear logic for orientation (units, $!$, $?$). Rust: `(A, B)` is
$\otimes$; $A \mathbin{\&} B$ is an offer of either, sharing the same resources
(a value with two consuming methods, or a closure taking a choice); `enum` is
$\oplus$; `FnOnce(A) -> B` is $A \multimap B$. Rust: the `linlogic` crate, proof
search in the sequent calculus for linear and affine propositional logic
(multiplicative-additive fragment), showing $A \vdash A \otimes A$ unprovable,
$A \otimes B \vdash A$ provable only with weakening, $A \mathbin{\&} B \vdash A$
provable. Lean: formulas, a linear sequent calculus as an inductive relation,
and a proof that $A \vdash A \otimes A$ is not derivable (a counting invariant on
atoms).
Code: crate `linlogic` + `crates/linlogic/examples/ch21_prover.rs`; Lean
`Book/Ch21/Linear.lean`.

### Chapter 22 · The Affine Lambda Calculus (`22-affine-lambda.md`)
$\lambda^{\mathsf{aff}}$: syntax (variables, λ, application, unit, $\otimes$ pairs
with a `let (x, y) = e in e'` eliminator, $\mathbin{\&}$ pairs with projections,
sums), typing rules with context splitting, weakening allowed, contraction
absent. Metatheory: the **usage theorem** (every variable is used at most once),
substitution lemma, preservation (sketch). Worked examples: swap is typable,
`dup` is not, discarding is. Why $\otimes$ has no projections (the orphaned
component), and how Rust's partial moves refine this per place. Algorithmic
checking with input/output contexts ("leftovers"). Rust: the `affine` crate, an
affine type checker with error messages modeled on E0382 ("use of moved
variable"). Lean: typing with context splitting as an inductive relation; the
usage theorem proved; an algorithmic checker and (if feasible) its soundness.
Code: crate `affine` + `crates/affine/examples/ch22_affine_checker.rs`; Lean
`Book/Ch22/Syntax.lean`, `Book/Ch22/Typing.lean`, `Book/Ch22/Usage.lean`,
`Book/Ch22/Checker.lean`.

### Chapter 23 · Copy, Clone and the Exponential (`23-copy-clone-exponential.md`)
The exponential modality $!A$: promotion, dereliction, weakening and contraction
for $!$-formulas. `Copy` as implicit, free contraction on a sub-class of types
(bitwise duplication; all fields `Copy`; no `Drop`; `&T` is `Copy`, `&mut T` is
not; E0204, E0184). `Clone` as explicit, possibly effectful duplication (a term of
type $\tau \multimap \tau \otimes \tau$). `Rc`/`Arc` as counted sharing. The
formal statement: $\lambda^{\mathsf{aff}}$ extended with a `Copy` predicate on
types and a splitting rule that may duplicate `Copy` variables. Rust: extend the
`affine` crate with `Copy` types. Lean: extend the Chapter 22 formalization with a
`Copy` predicate; the generalized usage theorem (non-`Copy` variables are used
at most once).
Code: crate `affine` (Copy support) + `crates/affine/examples/ch23_copy.rs`;
`examples/ch23_copy_clone.rs` (Copy vs Clone vs Rc in practice); compile-fail
`ch23_copy_with_drop.rs` (E0184), `ch23_copy_string_field.rs` (E0204); Lean
`Book/Ch23/Exponential.lean` (imports Chapter 22's files).

### Chapter 24 · Drop: Weakening with a Side Effect (`24-drop.md`)
Discarding is not free: destructors and RAII (files, locks, guards), drop glue,
drop order (locals in reverse declaration order, fields in declaration order,
temporaries), moves cancel drops (drop flags), `mem::drop`, `ManuallyDrop`.
Affine, not linear: `mem::forget` is safe; the history (the "leakpocalypse" and
`thread::scoped`), `Rc` cycles leak, why safety cannot depend on destructors
running (and `std::thread::scope` as the closure-based fix). What linearity
would buy (values that must be consumed), `#[must_use]` as a lint-level
approximation, ongoing language-design discussion (status: check). "Affine in
typing, linear in dynamics." Lean: no destructors; reference counting; in-place
updates of unshared values (functional but in place), demonstrated with
`dbgTraceIfShared` or an observable difference; a model in Lean: an evaluator for
a tiny resource language with a drop log, proving that no resource is released
twice, and that `forget` breaks "exactly once".
Code: `examples/ch24_drop_order.rs`, `examples/ch24_leaks_and_scopes.rs` (`Rc`
cycles and `Weak` counts, `mem::forget`, `thread::scope`); compile-fail
`ch24_use_after_drop.rs` (E0382); Lean `Book/Ch24/DropLog.lean`,
`Book/Ch24/InPlace.lean`.

### Chapter 25 · Typestate: Protocols in Types (`25-typestate.md`)
Protocol violations as type errors. Typestate with consuming methods (the old
state cannot be reused because values are affine), states as type parameters
with `PhantomData`, sealed traits for state sets, builders with required fields.
Session types (brief: duality). Where affinity falls short: Rust cannot force a
protocol to be completed (drop a half-finished connection); mitigations
(`#[must_use]`, a `Drop` that complains). Lean: indexed families
(`Conn : State → Type`), states that depend on runtime values (a vault indexed by
its balance), protocols as inductive relations, a proof that every accepted
trace ends in a final state. Domain: a connection (Closed → Connected →
Authenticated), a request builder, a lab instrument (Idle → Calibrated →
Measuring).
Code: `examples/ch25_typestate.rs`, `examples/ch25_builder.rs`; compile-fail
`ch25_use_after_close.rs` (E0382), `ch25_wrong_state.rs` (E0599); Lean
`Book/Ch25/Typestate.lean`.

## Part VI — Borrowing and Regions

### Chapter 26 · References, Aliasing and Regions (`26-references-regions.md`)
What breaks when a language has references into memory: dangling pointers,
use-after-free, iterator invalidation, data races; the principle "aliasing XOR
mutation". Why affinity alone cannot explain references: `&T` is `Copy`, freely
duplicable. Region calculi (Tofte and Talpin; Cyclone); lifetimes as region
variables; outlives constraints `'a: 'b`; the escape check (E0515, E0597, E0106);
elision rules; `'static`. Permissions, not multiplicities: a shared reference is
a duplicable read permission, a mutable reference a unique (affine) write
permission; a borrow is a temporary transfer of permission. Interior mutability
(`Cell`, `RefCell`) moves the check to run time. Lean: a toy imperative language
with a heap (explicit allocation and free), an operational semantics that gets
stuck on use-after-free, a program that goes wrong, and a simple region
discipline that rejects it.
Code: `examples/ch26_aliasing.rs`; compile-fail `ch26_dangling.rs` (E0597),
`ch26_return_local_ref.rs` (E0515), `ch26_shared_then_mut.rs` (E0502),
`ch26_two_mut.rs` (E0499), `ch26_iterator_invalidation.rs` (E0502); Lean
`Book/Ch26/Heap.lean`, `Book/Ch26/Regions.lean`.

### Chapter 27 · Subtyping and Variance (`27-subtyping-variance.md`)
The subsumption rule; subtyping is a preorder (a category). Rust's only subtyping
is between lifetimes (`&'static T` can be used as `&'a T`). Variance: covariant,
contravariant, invariant (and bivariant); the variance of `&'a T`, `&'a mut T`,
`fn(T) -> U`, `Box<T>`, `Cell<T>`, `*mut T`; why `&mut T` must be invariant in `T`
(the classic unsound program, rejected); variance inference for structs;
`PhantomData` to choose variance. Variance as functoriality: covariant and
contravariant functors on the preorder category of lifetimes (back to Chapter 17).
Coercions are not subtyping (deref coercion, unsizing, `&mut T` to `&T`). Lean: no
subtyping; coercions (`Coe`, `↑`) and subtypes `{x // p x}` (refinements, a
different idea). A tiny language with subtyping formalized in Lean (e.g. a top
type and function types), with a proof that the variance of the function type is
what makes subsumption sound; variances as a small monoid under composition.
Code: `examples/ch27_variance.rs`; compile-fail `ch27_mut_invariance.rs`
(lifetime error; check code), `ch27_contravariance.rs` (check code); Lean
`Book/Ch27/Subtyping.lean`, `Book/Ch27/Variance.lean`.

### Chapter 28 · A Core Calculus for Borrowing (`28-core-borrow-calculus.md`)
$\lambda^{\mathsf{aff}}_{\mathsf{rgn}}$, a small calculus with moves, drops, `Copy`,
shared borrows, mutable borrows, lifetimes and reborrowing (in the spirit of
Featherweight Rust and Oxide, simplified): syntax (owned values, `&'α τ`,
`&'α mut τ`, region variables, lexically scoped borrows, dereference, assignment
through `&mut`, reborrow); the `Copy` predicate and context splitting (shared
references are `Copy`, mutable ones are not); typing rules (borrow shared, borrow
mutable, deref, assign, reborrow, the escape check $\alpha \notin \mathrm{flv}(\sigma)$);
operational semantics (store, locations, borrowed places); metatheory statements
(progress and preservation, sketched). Worked derivation I: a `&mut` reborrow.
Worked derivation II: why the classic aliasing bug is rejected. Rust: the
`borrowck` crate, a checker for the calculus that prints derivations and errors.
Lean: the typing rules as an inductive relation; derivation I constructed as a
proof term; derivation II shown impossible (a proof that *no* derivation exists,
by inversion); a small metatheorem (in a well-typed term a mutable borrow
variable is used at most once).
Code: crate `borrowck` + `crates/borrowck/examples/ch28_borrowck.rs`; Lean
`Book/Ch28/Syntax.lean`, `Book/Ch28/Typing.lean`, `Book/Ch28/Derivations.lean`.

### Chapter 29 · How rustc Really Checks Borrows (`29-rustc-borrow-checking.md`)
A type system vs an analysis. The rustc pipeline: type checking with lifetimes as
inference variables, lowering to MIR (a control-flow graph of basic blocks,
places, `StorageLive`/`StorageDead`, drops); move analysis as a dataflow problem
(maybe-initialized places → E0382); liveness; non-lexical lifetimes (regions as
sets of CFG points, outlives constraints solved over points, loans live while a
reference may still be used); conflicts → E0499, E0502, E0506; two-phase borrows
(`v.push(v.len())`); "NLL problem case #3" (conditionally returning a borrow),
still rejected; Polonius as a Datalog formulation over origins and loans
(relations such as `loan_live_at` and `subset`) and its status (described with
care: check the current status). Rust: the `mini-nll` crate: a miniature MIR,
hand-built CFGs for real Rust snippets, a generic dataflow framework, move
analysis, liveness and loan conflict detection reporting rustc-like errors;
lexical vs non-lexical results on the same programs; problem case #3. Lean:
dataflow as a monotone fixpoint on a finite lattice, an iterative solver with
fuel, run on the same CFG with `#eval`, and a theorem that a converged result is
a fixpoint.
Code: crate `mini-nll` + `crates/mini-nll/examples/ch29_nll.rs`;
`examples/ch29_nll_accepts.rs` (real Rust that NLL and two-phase borrows accept);
compile-fail `ch29_problem_case_3.rs` (E0499 or E0502: check); Lean
`Book/Ch29/Dataflow.lean`.

## Part VII — Beyond

### Chapter 30 · Dependent Types (`30-dependent-types.md`)
Types that mention terms; Π-types (dependent functions) and Σ-types (dependent
pairs); indexed families vs parameters. Lean's native support: `Vector α n`,
`Fin n`, indexing with proof obligations (`xs[i]` and `xs[i]'h`), the equality
type `a = b`, rewriting (`▸`, `rw`), definitional vs propositional equality,
decidable equality. The λ-cube and where Rust, Haskell and Lean sit. Rust's
approximations: const generics (`[T; N]`, a `Matrix<R, C>` type with checked
multiplication), what is unstable (`generic_const_exprs`: no `N + M` in stable
Rust), Peano naturals at the type level with traits and associated types,
length-indexed vectors with `PhantomData`, Σ-types as hiding the index (a
runtime-length `Vec`), "parse, don't validate" newtypes as poor-man's refinement
types. Lean: dimension-indexed matrices from scratch, compared with Mathlib's
`Matrix (Fin m) (Fin n) α`.
Code: `examples/ch30_const_generics.rs`, `examples/ch30_type_level_nat.rs`;
compile-fail `ch30_matrix_mismatch.rs` (E0308), `ch30_const_arithmetic.rs`
(generic parameters in const operations: check code); Lean
`Book/Ch30/Vectors.lean`, `Book/Ch30/Equality.lean`, `Book/Ch30/Matrix.lean`.

### Chapter 31 · Proving Programs Correct (`31-proving-programs.md`)
Specifications as types. Induction on lists and trees; structural vs well-founded
recursion (`termination_by`, `decreasing_by`). A verified insertion sort (sorted
and a permutation of the input) and a verified binary search; results as
subtypes (`{ ys // Sorted ys ∧ Perm xs ys }`, with Mathlib's `List.Sorted` and
`List.Perm`); tactics in more depth (`induction ... generalizing`, `simp`
lemmas, `omega`, `linarith`, `ring`, `grind`, `calc`). Running
verified Lean code. The workflow "model in Lean, implement in Rust": the Rust
implementation tested against the model's outputs (differential testing). The
landscape of tools that verify Rust (Aeneas translates Rust to Lean; Verus,
Creusot, Prusti, Kani), described briefly and carefully. What a proof gives you
and what it does not (wrong specifications, trusted code).
Code: `examples/ch31_sort.rs` (insertion sort and binary search in Rust with
differential tests against expected outputs produced by the Lean model); Lean
`Book/Ch31/Sorting.lean`, `Book/Ch31/BinarySearch.lean`,
`Book/Ch31/Termination.lean`.

### Chapter 32 · Soundness, unsafe and Semantic Types (`32-soundness-semantic-types.md`)
Syntactic soundness (progress and preservation) and its limits. Semantic typing:
types as predicates on values (logical relations) and the fundamental theorem;
code that is semantically well typed but not syntactically (safe abstractions
over `unsafe`: `split_at_mut`, `Vec`, `Cell`). `unsafe` as a proof obligation
(safety vs validity invariants, `SAFETY:` comments). RustBelt: $\lambda_{\mathrm{Rust}}$,
Iris (higher-order concurrent separation logic), the lifetime logic. Separation
logic basics: heaps, points-to, separating conjunction, the frame rule. Stacked
and Tree Borrows, Miri. What types do not guarantee. Where affinity reappears:
Iris is an *affine* separation logic ($P \ast Q \vdash P$). Lean: a logical
relation for a small language with a primitive that the syntactic type system
cannot check, and its fundamental lemma; a shallow separation logic (heaps as
finite maps, separating conjunction, commutativity and associativity, a frame
lemma, affinity of the model). Rust: `split_at_mut` and a `Cell`-like type with
careful `SAFETY` arguments; how to run Miri (not part of CI).
Code: `examples/ch32_unsafe_abstractions.rs`; Lean
`Book/Ch32/LogicalRelation.lean`, `Book/Ch32/SeparationLogic.lean`.

### Chapter 33 · The Verdict (`33-the-verdict.md`)
Back to the question. Three senses of "based on": historical, specificational,
implementational. Rust feature ↦ correct type-theoretic account (tables). Which
structural rules Rust keeps, for owned non-`Copy` values, `Copy` values, `&mut T`
and `&T`. How to say it correctly. The bigger picture: Rust's type system as a
federation of theories (ADTs, System F-style generics with type classes,
existentials, an affine core, regions and permissions, variance, const
generics); Lean's as one unified dependent type theory (universes, inductive
types, `Prop`). What each language taught us about the other. Where to go next.
Code: none required.

## Appendices

- **A · Setting Up Rust and Lean** (`A-setup.md`) — rustup and the pinned
  toolchain, elan and `lean-toolchain`, VS Code with rust-analyzer and the Lean 4
  extension (the infoview), running the examples and the verification tools,
  building the book.
- **B · Lean 4 for Rust Programmers: Cheat Sheet** (`B-lean-cheat-sheet.md`)
- **C · Notation and Dictionary** (`C-notation.md`) — every symbol used in the
  book; judgment forms; a logic / type theory / category theory / Rust / Lean
  dictionary.
- **D · The Tactics Used in This Book** (`D-tactics.md`)
- **E · Glossary** (`E-glossary.md`)
- **F · Further Reading** (`F-further-reading.md`) — annotated, classics only,
  with no invented details.
