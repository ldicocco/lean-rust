# Categories for Programmers

Look at the last program you wrote and count how often you composed two things.
An iterator chain such as `lines.iter().map(parse).filter(valid).collect()` is
four steps glued end to end. A web server passes a request through a stack of
middleware. A compiler is a pipeline: lexer, parser, type checker, code
generator. Even the humblest refactoring, extracting three lines into a helper
function, relies on a fact so obvious that nobody states it: gluing `f` to `g`
and then to `h` gives the same program however you group the steps. Composition
is what programmers do all day.

**Category theory** is the mathematics of composition. It studies things that
can be glued end to end, and deliberately forgets what they are made of. The
effect is the opposite of vagueness: by looking only at how arrows compose,
category theory finds definitions that work in many settings at once. One definition of "product" gives you pairs of values,
the minimum of two numbers and the conjunction of two propositions. One
definition of "terminal object" gives you `()`, `True` and the largest element of
an order. Part IV uses this language to explain `map` (Chapter 17), generic
functions (Chapter 18), closures and the λ-calculus (Chapter 19), and `?` with
`and_then` (Chapter 20). This chapter lays the foundation.

**In this chapter you will learn:**

- what a category is: objects, morphisms, identities, composition and the three
  laws, and how the book's `Category` class states them in Lean;
- many small examples: types and functions, preorders, monoids, discrete
  categories and the free category of paths in a graph, in Lean and in Rust;
- how to read commutative diagrams, and why a commuting square is a property
  test with a proof;
- isomorphisms, monomorphisms and epimorphisms, and what they are in the
  category of types;
- initial and terminal objects, products and coproducts, defined by universal
  properties and proved in Lean for `Empty`, `Unit`, pairs and sums, together
  with their uniqueness up to unique isomorphism;
- duality: the opposite category, and how it turns every theorem into two;
- how Mathlib's category theory library writes all of this (`⟶`, `≫`, `𝟙`,
  `Type u` as a category, products through `Limits`).

## Composition is what programmers do

Here is composition in Rust, written once for all types. The full program is in
`code/rust/examples/ch16_categories.rs`.

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:compose}}
```

`compose(g, f)` turns a function from `A` to `B` and a function from `B` to `C`
into a function from `A` to `C`. The argument order follows the mathematical
notation $g \circ f$, read "$g$ after $f$": the function on the right runs first
(Mathlib uses the opposite convention, as we will see at the end of the chapter).
The types must *meet*: the output type of `f` must be the input type of `g`.
`identity` does nothing, for every type. Two facts about these functions are so
familiar that they are easy to overlook:

- composing with `identity`, on either side, changes nothing;
- when you compose three functions, it does not matter which two you glue first.

The example checks both facts on a few inputs:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:function_laws}}
```

```text
{{#include ../../code/rust/output/ch16_categories.txt:1:2}}
```

The second fact is the one your refactorings rely on. If a pipeline does
`len`, then `double`, then `is_even`, you may extract the first two steps into a
helper (`compose(is_even, compose(double, len))`) or the last two
(`compose(compose(is_even, double), len)`), and the program means the same
thing. That is **associativity**. The first fact says that `identity` is a
neutral element for composition, like `0` for addition: the **unit laws**.

The checks never looked at what `len` or `double` compute, only at their source
and target types, at how they compose, and at the identity. Category theory keeps
exactly this and throws away the rest.

## The definition of a category

A **category** $\mathcal{C}$ consists of:

- a collection of **objects** $a, b, c, \dots$;
- for every two objects $a$ and $b$, a collection $\mathrm{Hom}(a, b)$ of
  **morphisms** (also called **arrows**) from $a$ to $b$; we write
  $f : a \to b$ for $f \in \mathrm{Hom}(a, b)$, and call $a$ the *source* and $b$
  the *target* of $f$;
- for every object $a$, an **identity** morphism $\mathrm{id}_a : a \to a$;
- for every $f : a \to b$ and $g : b \to c$, a **composite** $g \circ f : a \to c$.

These must satisfy three laws, for all $f : a \to b$, $g : b \to c$ and
$h : c \to d$:

$$
\mathrm{id}_b \circ f = f
\qquad\qquad
f \circ \mathrm{id}_a = f
\qquad\qquad
h \circ (g \circ f) = (h \circ g) \circ f
$$

That is the whole definition. Three remarks will save you confusion later.

First, composition is only defined when the arrows meet: $g \circ f$ exists only
if the target of $f$ is the source of $g$. This is exactly the type-checking rule
of `compose`.

Second, **objects need not be sets, and morphisms need not be functions.** In the
examples below you will meet categories whose morphisms are proofs of
inequalities, elements of a monoid, and paths in a graph. Morphisms are whatever
the category says they are, as long as they compose and obey the laws.

Third, category theory never looks *inside* an object. Everything it says about
an object, it says through the arrows that go in and out of it. This will turn
out to be a strength: it is why the same definitions work in so many places.

A small picture helps. The diagram shows three objects of the category of types
and some of the arrows between them: the identities (drawn as loops), `len`,
`isEven`, their composite, and `double`, an arrow from `ℕ` to itself that is not
the identity.

![A few objects and morphisms of the category of types. Loops are morphisms from an object to itself; the dashed arrow is the composite of the two solid arrows it bypasses.](../images/ch16-category.svg)

### The book's `Category` class

Here is the definition in Lean. It lives in `code/lean/Book/Ch16/Category.lean`,
the module that all the chapters of Part IV share:

```lean
{{#include ../../code/lean/Book/Ch16/Category.lean:category}}
```

Let us read it field by field.

- `class Category (Obj : Type u)` declares a type class (Chapter 14) indexed by
  the type of objects. An *instance* `Category Obj` says how the elements of
  `Obj` form a category. The universe variable `u` (Chapter 12) allows `Obj` to
  be big: the type of all types, `Type`, itself lives in `Type 1`, and we want
  `Type` to be a category.
- `Hom : Obj → Obj → Type` is the heart of the definition: for every two
  objects, a *type* of morphisms, which depends on the *values* `a` and `b` (a
  dependent type, in the sense of Chapter 1). This is why "composition only when
  the arrows meet" is checked by Lean's type checker for free.
- `id` and `comp` are the data: an identity for every object, and a composition
  for every two arrows that meet. The objects of `comp` are implicit
  arguments (in braces), because Lean can read them off the arrows. As the
  comment says, `comp g f` means "first `f`, then `g`", like $g \circ f$.
- `id_comp`, `comp_id` and `assoc` are the three laws, as **fields**: an instance
  is rejected until it supplies proofs of them. This is the difference between a
  Lean class and a Rust trait that Chapter 14 pointed out: a trait can list
  operations but not demand laws.

Why does `Hom` land in `Type`, rather than in an arbitrary universe as in
Mathlib? For simplicity: every category in this book has morphisms that fit in
`Type`, and a fixed universe keeps universe annotations out of every statement.
The price is that a category whose arrows between two objects are too many to
form a `Type` cannot be an instance; we will not need one. The choice also has a
pleasant consequence that Chapter 17 uses: since `Hom a b` is a type, it is an
object of the category of types.

Two notations make statements readable:

```lean
{{#include ../../code/lean/Book/Ch16/Category.lean:notation}}
```

`a ⟶ b` (a long arrow, typed `\hom` in the editor) is the type of morphisms from
`a` to `b`, and `g ⊚ f` (typed `\oo`) is their composite. Both are `scoped`: they
are active inside `namespace Ch16` and in files that `open Ch16`, and nowhere
else, so that they do not leak into the rest of the book. `infixr` makes them
right-associative, and the numbers are precedences: `⟶` binds more loosely than
almost everything, like `→`.

### The category of types

The first instance is the one we started with:

```lean
{{#include ../../code/lean/Book/Ch16/Category.lean:type_category}}
```

The objects are the Lean types in `Type`, the morphisms from `α` to `β` are the
functions `α → β`, the identity is `fun x => x`, and composition is function
composition. All three laws are proved by `rfl`. Why does that work? Take
`id_comp`: the left side, `comp (id b) f`, unfolds to `fun x => (fun y => y) (f x)`,
which computes (by β-reduction) to `fun x => f x`. Lean's definitional equality
includes η for functions, so `fun x => f x` *is* `f`. Associativity is similar:
both sides compute to `fun x => h (g (f x))`. The laws of the category of types
hold "by computation", which is why programmers never notice them.

With the instance in place, functions can be written and composed as morphisms.
The file `code/lean/Book/Ch16/Examples.lean` starts with:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:type_examples}}
```

The declared type `String ⟶ ℕ` unfolds to `String → ℕ`, so an ordinary function
can be its value. The composite `isEven ⊚ double ⊚ len` parses as
`isEven ⊚ (double ⊚ len)` and runs from right to left: the length of `"abc"` is
3, doubled is 6, which is even. Because the laws hold by computation, specific
instances of them are `rfl` too:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:type_laws}}
```

### Rust types and functions, with caveats

Do Rust's types and functions (or closures) form a category in the same way,
with `identity` and `compose`? Approximately, and the approximation is
instructive, because a Rust function is more than a mapping from inputs to
outputs:

- **Side effects.** A function can print or mutate shared state. Composition
  stays associative, but "two morphisms are equal" now has to mean "the same
  outputs *and* the same effects", and we will see that this breaks one of the
  nicest facts about `()`.
- **Panics and non-termination.** `|_| panic!()` and `|_| loop {}` have type
  `A -> B` for every `B`, but never return a `B`.
- **Equality of functions is not checkable.** Lean proves `f = g` with `funext`
  (functions that agree on every input are equal); a Rust test compares outputs
  on samples.
- **Ownership.** A function `fn(A) -> B` consumes its argument. Composition is
  unaffected, but products will show where it matters.

The usual way out is to reason about the *pure, total* fragment: functions that
always return and have no observable effects. Within it, Rust types and functions
form a category as honestly as Lean's do, and we will point out each place where
stepping outside changes the answer.

## A gallery of categories

The category of types is only one example, and if it were the only one, category
theory would be pointless. This section collects small categories that look
nothing like it. Each comes in Lean (as an instance of the book's class, with its
laws proved) and most come in Rust too.

### Categories as data, in Rust

In Rust we cannot write `Hom(a, b)` as a *type* that depends on the *values*
`a` and `b`: that needs dependent types, the subject of Chapter 30. What we can
do is represent a category whose objects and morphisms are runtime values, and
check at run time that two morphisms meet before composing them:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:category_trait}}
```

With the trait, a single generic function can test the laws of every instance on
sample morphisms. It checks the two unit laws for every sample, and
associativity for every triple of samples that can be composed:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:check_laws}}
```

The contrast with Lean is worth stating once. In Lean, composing two arrows that
do not meet is a *type error*, caught before the program runs. In Rust it is a
`None` at run time. In Lean the laws are proved for all morphisms; in Rust they
are tested on the samples we thought of.

### Preorders

A **preorder** is a relation $\le$ that is reflexive ($a \le a$) and transitive
($a \le b$ and $b \le c$ give $a \le c$). Every preorder is a category:

- the objects are the elements;
- there is exactly one morphism $a \to b$ when $a \le b$, and none otherwise;
- the identity on $a$ is reflexivity, $a \le a$;
- composition is transitivity.

The laws hold automatically, because between two objects there is at most one
morphism, so any two parallel morphisms are equal. A category with this property
is called **thin**. Examples are everywhere: numbers with $\le$; positive integers
ordered by divisibility; propositions ordered by implication ($p \le q$ when $p$
implies $q$); and, in Chapter 27, Rust's lifetimes ordered by "outlives", where
`'a: 'b` says that `'a` lasts at least as long as `'b`.

In Lean, a morphism $a \to b$ is a *proof* of `a ≤ b`:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:preorder}}
```

`Preorder α` is Mathlib's class of preorders: a relation `≤` with the lemmas
`le_refl` and `le_trans`. A proof of `a ≤ b` lives in `Prop`, but `Hom` must
return a `Type`, so we wrap it with `PLift`, a structure with a single field
`down` that turns anything (including a proof) into a value of a type in `Type`:
`⟨h⟩` builds one, and `f.down` takes it apart. The laws are `rfl` because of **proof irrelevance** (Chapter 10):
any two proofs of the same proposition are definitionally equal, so
`⟨le_trans f.down (id b).down⟩` and `f` are the same morphism as far as Lean is
concerned.

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:preorder_examples}}
```

`threeToFive` is the morphism $3 \to 5$ in the category `ℕ`; its "content" is
a proof that `3 ≤ 5`, found by `decide`. `preorder_thin` states thinness. Its
proof needs one step more than `rfl`: `cases f` and `cases g` take the two
morphisms apart into `⟨h₁⟩` and `⟨h₂⟩` (Lean's `rfl` does not see through two
unknown structures at once), and then `rfl` succeeds because `h₁` and `h₂` are
proofs of the same proposition. Finally, `andElim` is a morphism in `Prop`,
where Mathlib defines `p ≤ q` as `p → q`: its content is the proof
`fun h => h.1` of $p \land q \to p$.

The Rust version uses divisibility. A morphism carries its source and target,
and the only way to build one is through `divides`, which checks the relation:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:divisibility}}
```

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:use_divisibility}}
```

```text
{{#include ../../code/rust/output/ch16_categories.txt:3:4}}
```

The samples are all the divisibility facts among the numbers 1 to 12, and the
checker verified 203 equations: two unit laws for each sample morphism, and
associativity for every composable triple.

### Monoids are categories with one object

A **monoid** is a set $M$ with an associative operation $\cdot$ and a unit
element $e$: $e \cdot x = x = x \cdot e$ and $x \cdot (y \cdot z) = (x \cdot y) \cdot z$.
Examples: numbers with $+$ and $0$ or with $\times$ and $1$, strings with
concatenation and `""`, and functions from a type to itself with composition and
the identity.

Compare the monoid laws with the category laws: they are the same equations.
That is not a coincidence. A monoid *is* a category with exactly one object
$\star$: the morphisms $\star \to \star$ are the elements of $M$, composition is
the operation, and the identity is the unit. Since there is only one object,
every two morphisms meet, and the "type-checking" part of composition
disappears.

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:one_object}}
```

`OneObject M` is a structure with no fields, so it has exactly one value,
written `⟨⟩`: the single object. `Monoid M` is Mathlib's class of monoids, which
provides `*`, `1` and the three laws `one_mul`, `mul_one` and `mul_assoc`
(Chapter 14 built its own version of this class). Each category law is
discharged by the corresponding monoid law; associativity is stated the other way
around in Mathlib, hence the `.symm`, which turns a proof of $x = y$ into a proof
of $y = x$.

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:one_object_eval}}
```

`OneObject.arrow` only tells Lean the type of the (single) object. Composing the
arrows `2` and `3` in the one-object category of $(\mathbb{N}, \times, 1)$
multiplies them.

The connection runs the other way too. In *any* category, the morphisms from an
object to itself (its **endomorphisms**) form a monoid under composition, and the
monoid laws are instances of the category laws:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:endo_monoid}}
```

The proof is the three laws, glued with the anonymous constructor `⟨_, _, _⟩`
that builds a conjunction. So the functions `ℕ → ℕ`, such as `double` in the
picture above, form a monoid.

In Rust, strings under concatenation give a one-object category whose single
object is `()`:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:string_monoid}}
```

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:use_strings}}
```

```text
{{#include ../../code/rust/output/ch16_categories.txt:5:6}}
```

`compose(g, f)` puts `f`'s text first, to match "first `f`, then `g`"; the other
choice would give a perfectly good category too, as duality will explain.

### Discrete categories

At the other extreme from a monoid is a category with many objects and no
interesting arrows: the only morphisms are the identities. Any set gives such a
**discrete category**. In Lean a morphism $a \to b$ is a proof that $a = b$:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:discrete}}
```

`Discrete α` is a copy of `α` (a structure with one field), so that the instance
does not compete with other instances on `α`, such as the preorder on `ℕ`.
Composition is transitivity of equality. The theorem `discrete_no_arrow` shows that there is no
morphism between two different objects: from `f` we extract a proof `h` of
`⟨1⟩ = ⟨2⟩`, and `simp at h` simplifies it. `simp` knows that two values built
with the same constructor are equal only if their fields are, turns `h` into
`1 = 2`, evaluates that to `False`, and a hypothesis `False` closes any goal.

Discrete categories look trivial, and they are; they serve as building blocks. A
pair of objects of a category is the same thing as a way of sending the two
objects of a two-element discrete category into it, a remark that Mathlib's
`Limits` library turns into its definition of products.

### Free categories: paths in a graph

Take a directed graph: vertices, and edges between them. Its **paths** form a
category. The objects are the vertices; a morphism from $a$ to $b$ is a path
that starts at $a$ and ends at $b$ (a sequence of edges, each starting where the
previous one ended); composition is concatenation; the identity on $a$ is the
empty path at $a$. This is the **free category** on the graph: "free" because
it satisfies no equations beyond the laws, so two paths are equal only if they
consist of the same edges.

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:path}}
```

`Path E` is an *inductive family*: one type `Path E a b` for every pair of
vertices, defined all at once, like the typing relations of Chapter 3 but in
`Type` rather than `Prop`. A path is either `nil a`, the empty path at `a`, or
`cons e p`, an edge from `a` to `b` followed by a path from `b` to `c`; the type
of `cons` makes it impossible to build a path whose edges do not meet. `append`
concatenates by recursion on the first path (the leading `_` in its patterns
stand for the implicit vertices).

The laws are theorems about `append`:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:path_laws}}
```

`nil_append` is `rfl`: it is literally the first equation of `append`. The other
unit law is not: `append p (nil b)` is stuck until we know whether `p` is `nil`
or `cons`, so we prove it by induction on `p`. In the `nil` case both sides are
`nil a`. In the `cons e p` case, `simp only [append]` unfolds one step of the
definition, leaving `cons e (append p (nil _)) = cons e p`, and the induction
hypothesis `ih : append p (nil _) = p` rewrites the left side into the right.
Associativity is the same pattern; there `simp only [append, ih]` unfolds and
rewrites with the hypothesis in one go.

Now the instance:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:free_category}}
```

The wrapper `Free E` attaches the instance to the graph, since the vertex type `V`
alone does not say which edges we mean. Note the order in
`comp g f := Path.append f g`: the path walks `f` first. Because of that order,
the category's left unit law (`id ⊚ f = f`) is `append_nil` and its right unit
law is `nil_append`.

Here is a graph that every network programmer knows: the states of a connection
and the operations that move between them.

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:protocol}}
```

`Step` is an inductive family again: `Step a b` is the type of operations that
go from state `a` to state `b`, so `Step.login` exists only from `.connected`
to `.authenticated`. A morphism of the free category, a `Trace`, is a sequence of
operations that the protocol allows. Composing `signIn` with `signOut` gives the
whole session. Composing `signIn` with itself is not "an error at run time": it
does not type-check, because `signIn` ends at `.authenticated` and starts at
`.closed`. Chapter 25 builds whole APIs on this idea, under the name typestate.

The Rust version represents the same graph as a transition function, and traces
as vectors of operations validated when they are built:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:protocol_graph}}
```

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:protocol_trace}}
```

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:protocol_category}}
```

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:use_protocol}}
```

```text
{{#include ../../code/rust/output/ch16_categories.txt:7:9}}
```

The composite session is the four operations in order; composing `sign_in` with
itself gives `None`, the run-time counterpart of Lean's type error.

## Commutative diagrams

Equations between composites quickly become hard to read, so category theorists
draw them. A **diagram** is a picture of some objects and some arrows between
them. A diagram **commutes** if any two paths of arrows with the same start and
the same end compose to the same morphism.

Here is a commutative square from everyday programming. Start with a pair of
lists. You can append them and take the length of the result, or take the two
lengths and add them:

![A commutative square: appending two lists and then measuring the result gives the same number as measuring both lists and adding.](../images/ch16-square.svg)

The square commutes: both paths from the top-left corner to the bottom-right
corner are the same function. In Lean, that is one equation between composites:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:square}}
```

The proof uses `funext p`, which reduces an equation between functions to an
equation between their values at an arbitrary argument `p`, and then Lean's
library lemma `List.length_append`, which says exactly
`(p.1 ++ p.2).length = p.1.length + p.2.length`.

If you have written property-based tests, you have written commutative diagrams
without the pictures: "for all pairs of lists, `len(a ++ b) == len(a) + len(b)`"
is this square, tested on random samples, while the Lean version is proved for
all inputs. Chapter 18 is full of such squares, under the name naturality
squares.

## Isomorphisms

When are two objects "the same"? Category theory must answer with arrows. A
morphism $f : a \to b$ is an
**isomorphism** if it has an **inverse** $g : b \to a$:

$$
g \circ f = \mathrm{id}_a
\qquad\qquad
f \circ g = \mathrm{id}_b
$$

Then $a$ and $b$ are **isomorphic**, written $a \cong b$, and nothing category
theory can say distinguishes them. You have seen this idea in Chapter 11, where
`Iso` structures recorded that types such as `A × ()` and `A` carry the same
information: isomorphisms in the category of types. The shared module
generalizes the definition to every category:

```lean
{{#include ../../code/lean/Book/Ch16/Category.lean:iso}}
```

An `Iso a b` packages the two arrows and the two equations; the module also
defines the notation `a ≅ b` for it. Isomorphism behaves like an equality: every
object is isomorphic to itself, and isomorphisms can be reversed and composed.
In `Iso.refl` both equations say `id a ⊚ id a = id a`, an instance of the unit
law; `Iso.symm` swaps the two arrows and the two proofs.

```lean
{{#include ../../code/lean/Book/Ch16/Category.lean:iso_refl}}
```

```lean
{{#include ../../code/lean/Book/Ch16/Category.lean:iso_trans}}
```

The proof of `inv_hom` in `Iso.trans` is a good exercise in reading `rw`. The
goal is `(i.inv ⊚ j.inv) ⊚ (j.hom ⊚ i.hom) = id a`: undo `j`, undo `i`, after
doing `i` and then `j`. The rewrites move the brackets until the inner pair meets:

1. `Category.assoc` rewrites the left side, of the shape `h ⊚ (g ⊚ f)`, into
   `((i.inv ⊚ j.inv) ⊚ j.hom) ⊚ i.hom`.
2. `← Category.assoc i.inv` uses the same law from right to left, on the
   subterm that starts with `i.inv`: `(i.inv ⊚ j.inv) ⊚ j.hom` becomes
   `i.inv ⊚ (j.inv ⊚ j.hom)`.
3. `j.inv_hom` replaces `j.inv ⊚ j.hom` with `id b`.
4. `Category.comp_id` removes it: `i.inv ⊚ id b` becomes `i.inv`.
5. `i.inv_hom` turns `i.inv ⊚ i.hom` into `id a`, and the goal `id a = id a`
   is closed by `rfl`, which `rw` tries automatically.

The proof of `hom_inv` is the mirror image. Neither mentions what the objects or
the morphisms are: they hold in every category at once.

Two isomorphisms in the category of types:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:iso_examples}}
```

For `boolIso`, the equations compare two functions, so `funext b` reduces them
to a statement about an arbitrary `b : Bool`, `cases b` splits into the cases
`false` and `true`, and `<;> rfl` runs `rfl` on both. For `swapIso` the equations
hold by computation (swapping twice gives back the pair, by η for pairs).

A morphism can have at most one inverse. The proof is a classic of
equational reasoning, written here with `calc`, which chains equations step by
step, each with its own justification:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:inverse_unique}}
```

Read the chain from top to bottom: insert an identity, replace it by $f \circ g'$,
regroup, replace $g \circ f$ by an identity, remove it. Each `_ = ...` line
continues from the right-hand side of the previous one. So "the inverse" of an
isomorphism is well defined, which is why `Iso` can store it as a field.

In a preorder, $a \cong b$ means $a \le b$ and $b \le a$. In an order where
that forces $a = b$ (a partial order, such as `ℕ`), the only isomorphisms are
identities.

## Monomorphisms and epimorphisms

Injective and surjective functions have categorical versions stated with arrows
only. A morphism
$f : a \to b$ is a **monomorphism** (mono) if it can be cancelled on the left,
and an **epimorphism** (epi) if it can be cancelled on the right:

$$
f \circ g = f \circ h \;\Rightarrow\; g = h
\qquad\qquad
g \circ f = h \circ f \;\Rightarrow\; g = h
$$

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:mono_epi}}
```

In the category of types these are exactly the injective and the surjective
functions. Here is the first half:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:mono_injective}}
```

`constructor` splits the `↔` into two implications.

- *Mono implies injective.* We have `hf : Mono f` and `x y` with `f x = f y`,
  and must show `x = y`. The trick is to test cancellation with two functions
  out of `Unit`: the constant functions `fun _ => x` and `fun _ => y`. Composing
  them with `f` gives `fun _ => f x` and `fun _ => f y`, which are equal by
  `funext` and the hypothesis. Mono cancels `f`, so the two constant functions
  are equal, and `congrFun h ()` applies both sides to `()` to get `x = y`.
  (Functions out of `Unit` are the categorical stand-in for elements, a trick you
  will see again.)
- *Injective implies mono.* Given `f ∘ g = f ∘ h`, compare `g` and `h` at any
  `t`: `congrFun hgh t` gives `f (g t) = f (h t)`, and injectivity removes `f`.

And the second half:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:epi_surjective}}
```

- *Epi implies surjective.* Given `b`, we want some `a` with `f a = b`. We test
  cancellation with two functions from `β` into `Prop` (which is itself a type,
  so it is an object of our category): `g y` is the proposition "`y` is hit by
  `f`", and `h y` is `True`. Composed with `f` they agree, since every `f a` is
  hit by `f`: `eq_true` turns the proof `⟨a, rfl⟩` of `∃ a', f a' = f a` into the
  equation `(∃ a', f a' = f a) = True`. Epi cancels `f`, so `g = h`; at `b` this
  says `(∃ a, f a = b) = True`, and `of_eq_true` turns that back into a proof.
- *Surjective implies epi.* To compare `g` and `h` at `b`, write `b` as `f a`
  (`obtain ⟨a, rfl⟩ := hf b` both extracts `a` and replaces `b` by `f a`
  everywhere), and use the hypothesis at `a`.

Do not conclude that "mono and epi" means "isomorphism", as "injective and
surjective" means "bijective" for functions. In a preorder, any two parallel
morphisms are equal, so *every* morphism is both mono and epi; but $0 \le 1$ in
`ℕ` is not an isomorphism, because there is no morphism back:

```lean
{{#include ../../code/lean/Book/Ch16/Examples.lean:mono_epi_not_iso}}
```

The last proof extracts from the inverse a proof of `1 ≤ 0`, and `omega` (the
decision procedure for linear arithmetic of Chapter 2) finds the contradiction.
Categorical definitions agree with the familiar ones in the category of types and
can behave very differently elsewhere.

## Initial and terminal objects

Some objects are characterized by the arrows around them alone. An object $t$ is
**terminal** if from every object $a$ there is *exactly one* morphism $a \to t$.
Dually, an object $i$ is **initial** if to every object $a$ there is exactly one
morphism $i \to a$.

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:terminal}}
```

The definitions live in `code/lean/Book/Ch16/Universal.lean`. Each is a
structure with the morphism (`arrow`) and a proof that it is the only one
(`unique`). In the category of types, `Unit` is terminal and `Empty` is initial:

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:unit_empty}}
```

For `Unit` there is only one function from any type: the one that returns `()`.
Any other function `f` agrees with it everywhere, because `Unit` has only one
value, so after `funext x` the goal `f x = ()` is closed by `rfl` (Lean has η
for `Unit`: every value of `Unit` is definitionally `()`). For `Empty` there is
exactly one function *to* any type, the empty function: `nomatch e` is a match
with no cases, accepted because `Empty` has no constructors. Uniqueness is
vacuous: two functions out of `Empty` agree on all of the (zero) inputs.

Rust has both, and Chapter 1's table already named them:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:terminal_initial}}
```

`match v {}` is Rust's `nomatch`: a `match` with no arms on a type with no
variants, which has every type. The logician reads these as `True` (provable from
anything) and `False` (from which anything follows): in the category `Prop`,
`True` is terminal and `False` is initial.

Not every category has these objects. In `ℕ` with `≤`, `0` is initial, since
`0 ≤ n` for every `n`; but there is no terminal object, since no number is above
every number:

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:nat_terminal}}
```

Uniqueness for `0` is `preorder_thin` again. For the negative result, a terminal
`n` would have an arrow from `n + 1`, that is, a proof of `n + 1 ≤ n`, which
`omega` refutes.

Now the side effects come back, as promised. In pure code, a function into `()`
carries no information, which is what "exactly one morphism into `()`" says. In
Rust, two functions into `()` can differ:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:effects}}
```

```text
{{#include ../../code/rust/output/ch16_categories.txt:15:15}}
```

`quiet` and `noisy` return the same value on every input, yet they are different
programs. Once effects count, `()` is no longer terminal. This is the first sign
of a theme of Chapter 20: effects need a category of their own.

### Unique up to unique isomorphism

How many terminal objects can a category have? Possibly many (any one-element
type is terminal in the category of types), but they are all isomorphic, and in
exactly one way:

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:terminal_unique}}
```

The whole argument rests on `hom_ext`: two morphisms into a terminal object are
equal, because both are equal to the `arrow`. To build the isomorphism between
terminal objects $t_1$ and $t_2$, take the unique arrows in both directions.
Their composite $t_1 \to t_2 \to t_1$ is a morphism into the terminal object
$t_1$, and so is $\mathrm{id}_{t_1}$; by `hom_ext` they are equal. The same
argument works at $t_2$. And the isomorphism is unique because there is only one
morphism $t_1 \to t_2$ at all.

This pattern, "unique up to unique isomorphism", is the precise sense in which we
may speak of *the* terminal object.

## Products

Now the main event. What is a pair? In Rust, `(A, B)` is a type whose values
hold an `A` and a `B`. Category theory cannot look at values, so it describes
the pair type by what you can *do* with it: you can project out of it, and you can
build it from anything that gives you both components.

A **product** of objects $a$ and $b$ is an object $p$ with two morphisms
$\mathrm{fst} : p \to a$ and $\mathrm{snd} : p \to b$ such that for every object
$x$ and every pair of morphisms $f : x \to a$, $g : x \to b$, there is **exactly
one** morphism $\langle f, g \rangle : x \to p$ with

$$
\mathrm{fst} \circ \langle f, g \rangle = f
\qquad\qquad
\mathrm{snd} \circ \langle f, g \rangle = g
$$

In pictures, the left half of the next figure: whatever $x$, $f$ and $g$ are, the
dashed arrow exists, makes both triangles commute, and is the only arrow that
does. The right half is the coproduct, which we will meet next.

![The universal properties of the product (left) and the coproduct (right). The dashed arrow exists, is unique, and makes the triangles commute.](../images/ch16-universal.svg)

A definition of this shape is called a **universal property**. Think of it as an
interface specification: it does not say how a product is built, only what any
product must offer (two projections and a way to pair) and the laws these
operations satisfy. Any construction meeting the specification is a product, and
by the uniqueness theorem below, any two are interchangeable, with a canonical
translation between them. In Lean the specification is a structure:

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:product}}
```

The four fields mirror the definition: `lift f g` is $\langle f, g \rangle$, the
next two fields are the two triangles, and `uniq` says that any `h` making both
triangles commute is the lift. Note that `IsProduct` is *data* (a structure in
`Type`, because `lift` is a function), not just a proposition: a proof that
something is a product comes with the recipe for pairing.

### Pairs are products

Now the theorem: Lean's pair type, with its projections, is a product in the
category of types.

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:pair_product}}
```

The named argument `(Obj := Type)` tells Lean in which category we work. Without
it Lean would have to guess the category from `Prod.fst`, whose type is a plain
function type. Then the fields:

- `lift f g` is the function that runs both `f` and `g` on the same input and
  pairs the results.
- `fst_lift` and `snd_lift` hold by computation: `(f x, g x).1` is `f x`.
- `uniq` is the real content. We have `h : x → α × β` with
  `hf : Prod.fst ⊚ h = f` and `hg : Prod.snd ⊚ h = g`, and must show
  `h = lift f g`. `funext x` reduces this to `h x = (f x, g x)`. `apply Prod.ext`
  says that two pairs are equal when their first components are equal and their
  second components are equal, leaving two goals. The first is
  `(h x).1 = f x`, which is `hf` evaluated at `x`: `congrFun hf x`. The second is
  the same with `hg`.

Uniqueness deserves a moment's thought: it says that *a function into a pair
type is determined by its two components*. There is no hidden third piece of
information that a pair could carry. The lift computes:

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:pair_lift_eval}}
```

### Products in Rust, and the price of a copy

In Rust the pairing function looks like this:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:product}}
```

Look at the bound `X: Clone`. The lift must give *the same input* to both `f` and
`g`, and a function `Fn(X) -> A` consumes its argument, so `x` must be
duplicated. In Lean using a variable twice is free; in Rust it is an operation
that not every type supports. (Taking `Fn(&X)` would share a reference instead,
a different trick with its own theory, the subject of Part VI.) The example
checks the two triangles and the uniqueness condition on samples:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:universal_checks}}
```

```text
{{#include ../../code/rust/output/ch16_categories.txt:10:14}}
```

The candidate `h` was written differently (`n.pow(2)` and a different `format!`),
and it agrees with `pair` on every sample, as uniqueness predicts.

The need for `Clone` is not a detail. The morphism $a \to a \times a$ that pairs
the identity with itself, $\langle \mathrm{id}, \mathrm{id} \rangle$, is called the
**diagonal**, and it is the categorical name for *using a value twice*. Logic
calls the same thing *contraction*. Rust's ownership system is, among other
things, a refusal to provide the diagonal for free. Chapter 19 makes this
precise, and Part V builds the whole affine story on it.

### Products are unique

Like terminal objects, products are unique up to a unique isomorphism, and the
proof has the same shape: everything follows from the uniqueness clause.

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:product_unique}}
```

Suppose $p$ (with `fst`, `snd`) and $q$ (with `fst'`, `snd'`) are both products of
$a$ and $b$. Each product can lift the other's projections, which gives arrows
$q \to p$ and $p \to q$. For `inv_hom` we must show that the round trip
$p \to q \to p$ is the identity. The trick is to show that *both* the round trip
and `id p` are lifts of `fst` and `snd` through $p$, so that `P.uniq` makes both
equal to `P.lift fst snd`:

- `h₁`: the round trip followed by `fst` is `fst`. The `rw` chain regroups with
  `Category.assoc`, then uses `P.fst_lift` (the projection of the lift into $p$
  is `fst'`) and `Q.fst_lift` (the projection of the lift into $q$ is `fst`).
  The same for `snd`. So by `P.uniq`, the round trip equals `P.lift fst snd`.
- `h₂`: `id p` followed by `fst` is `fst`, by `Category.comp_id`, and the same
  for `snd`. So `id p` also equals `P.lift fst snd`.
- `rw [h₁, h₂]` rewrites both sides of the goal into the same thing.

`iso_fst` adds that the isomorphism respects the projections; its proof is one
of the triangles of `Q`, `Q.fst_lift`. So the pair type is
not just *a* product of `α` and `β`; it is *the* product, in the only sense in
which category theory can say "the".

## Coproducts

Turn every arrow in the definition of a product around, and you get a
**coproduct**: an object $s$ with **injections** $\mathrm{inl} : a \to s$ and
$\mathrm{inr} : b \to s$, such that for every $f : a \to x$ and $g : b \to x$ there
is exactly one $[f, g] : s \to x$ with

$$
[f, g] \circ \mathrm{inl} = f
\qquad\qquad
[f, g] \circ \mathrm{inr} = g
$$

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:coproduct}}
```

In the category of types, the coproduct is the sum type: Rust's `enum` with two
variants, Lean's `α ⊕ β` with constructors `Sum.inl` and `Sum.inr`. The
morphism out of the sum (`desc`, for "descend") handles each case with the
corresponding function: it is a `match`.

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:sum_coproduct}}
```

Uniqueness is proved by cases: after `funext s`, a value of `α ⊕ β` is either
`inl a` or `inr b`, and in each case the hypothesis about the corresponding
triangle, evaluated at that value, is exactly the goal. The proof says that *a
function out of a sum is determined by what it does on each variant*, which is
why exhaustive `match` is a complete way to consume an `enum`.

In Rust:

```rust
{{#include ../../code/rust/examples/ch16_categories.rs:coproduct}}
```

No `Clone` this time: the input goes to exactly one of the two functions.
Products and coproducts are perfectly dual in the category of types, but not in
Rust: pairing needs a copy, case analysis does not. This asymmetry, the shadow of
the diagonal, reappears in Part V as the difference between the two conjunctions
of linear logic.

## Duality and the opposite category

You have now seen several pairs of definitions that are mirror images: terminal
and initial, product and coproduct, mono and epi. Category theory makes the mirror
into a construction. The **opposite** of a category $\mathcal{C}$, written
$\mathcal{C}^{\mathrm{op}}$, has the same objects and every arrow reversed: a
morphism $a \to b$ in $\mathcal{C}^{\mathrm{op}}$ is a morphism $b \to a$ in
$\mathcal{C}$, and composition is done in the other order.

```lean
{{#include ../../code/lean/Book/Ch16/Category.lean:opposite}}
```

`Op Obj` is a copy of `Obj` (one field, `unop`), so that the opposite category is
a different instance on a different type and the two structures never clash.
`Hom a b` is `b.unop ⟶ a.unop`, reversed. The identity is the old identity;
`comp g f` is `f ⊚ g`. The laws come from the original ones: the left unit law of
the opposite is the right unit law of the original (and vice versa), and
associativity is the original associativity read backwards (`.symm`).

The **duality principle** follows: a terminal object of $\mathcal{C}^{\mathrm{op}}$
is an initial object of $\mathcal{C}$, a product in $\mathcal{C}^{\mathrm{op}}$ is a
coproduct in $\mathcal{C}$, a mono in $\mathcal{C}^{\mathrm{op}}$ is an epi in
$\mathcal{C}$. So every theorem about terminal objects, applied to the opposite
category, *is* a theorem about initial objects. In Lean we can watch this
happen:

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:duality}}
```

`IsInitial.op` repackages an initial object of `C` as a terminal object of
`Op C`; the fields are the same terms, because the types agree once `Op` is
unfolded. `Iso.unop` turns an isomorphism in the opposite category back into one
in `C`, swapping `inv_hom` and `hom_inv`. And `IsInitial.iso`, the uniqueness of
initial objects, has **no proof of its own**: it is `IsTerminal.iso`, applied in
the opposite category. As an example of its use:

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:empty_iso}}
```

Duality halves the work of category theory. (It also explains the remark about
the string monoid: reversing the order of concatenation gives the opposite
category.)

## Putting it together: one definition, many products

A universal property is a single definition with many implementations. Let us
run this chapter's definitions on two more categories.

In `ℕ` ordered by `≤`, what is a product of `a` and `b`? It is an object $p$ with
morphisms $p \to a$ and $p \to b$ (so $p \le a$ and $p \le b$), such that any $x$
with $x \le a$ and $x \le b$ has a morphism to $p$ (so $x \le p$). That is the
*greatest lower bound*: `min a b`. Dually, the coproduct is `max a b`.

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:min_max}}
```

All the equations (`fst_lift`, `uniq` and so on) are discharged by
`preorder_thin`: in a thin category, parallel arrows are always equal, so the
triangles commute and uniqueness holds automatically. The entire content of the
universal property is in `lift`, which needs the lemma `Nat.le_min`
("$x \le \min(a, b)$ if and only if $x \le a$ and $x \le b$"); `.mpr` takes
the right-to-left direction of the `↔`.

In `Prop` ordered by implication, the product is conjunction and the coproduct
is disjunction:

```lean
{{#include ../../code/lean/Book/Ch16/Universal.lean:and_or}}
```

The lift of `andIsProduct` is the familiar introduction rule for $\land$ from
Chapter 4: from proofs of $x \to p$ and $x \to q$, a proof of $x \to p \land q$.
The projections are the elimination rules, and the coproduct's `desc` is the
elimination rule for $\lor$ (proof by cases). Natural deduction's rules for
conjunction and disjunction *are* the universal properties of products and
coproducts in the thin category of propositions.

Here is the comparison, with Rust's approximate answers in the last row:

| Category | Product | Coproduct | Terminal | Initial |
|---|---|---|---|---|
| Lean types | `α × β` | `α ⊕ β` | `Unit` | `Empty` |
| `ℕ` with `≤` | `min a b` | `max a b` | none | `0` |
| `Prop` with `→` | `p ∧ q` | `p ∨ q` | `True` | `False` |
| Rust types (pure code) | `(A, B)`, with `Clone` | `enum` | `()` | `Void`, `!` |

This is Chapter 1's table of three readings, now with a precise meaning for the
third column: each entry is defined by the *same* universal property, in a
different category. The rows also explain why the same algebra keeps showing up: $\min$ distributes
over $\max$, $\land$ over $\lor$, and `A × (B ⊕ C)` is isomorphic to
`(A × B) ⊕ (A × C)` (Chapter 11); all three are one statement, "products
distribute over coproducts", in three categories. Chapter 19 adds the missing
column, the exponential (function types, implication), and shows that Chapter 5's
Heyting algebras are exactly the thin categories that have all of these.

## In Mathlib

Everything in this chapter has a counterpart in Mathlib's category theory
library. The differences are generality (morphisms in any universe), automation,
and one notational choice that you must get used to.

### `CategoryTheory.Category`

Mathlib's class is `CategoryTheory.Category C`, for a type of objects `C`. Its
morphisms come from a more primitive class, `Quiver` (a type of arrows between
any two objects, without composition), and live in a universe `v` that you can
specify as `Category.{v} C`. Its notation:

- `X ⟶ Y` is the type of morphisms, as in the book;
- `𝟙 X` (typed `\b1`) is the identity on `X`;
- `f ≫ g` (typed `\gg`) is composition **in diagrammatic order**: first `f`,
  then `g`. It is the book's `g ⊚ f`.

The diagrammatic order matches how arrows are drawn and how pipelines are
written (`f ≫ g` reads like `x.f().g()`). The laws `id_comp`, `comp_id` and
`assoc` have *default proofs*: an instance that omits them makes Mathlib try a
tactic, `cat_disch`, that proves simple ones automatically. They are also `simp`
lemmas, so `simp` normalizes identities and brackets:

```lean
{{#include ../../code/lean/Book/Ch16/InMathlib.lean:mathlib_generic}}
```

These examples, and the ones below, are in `code/lean/Book/Ch16/InMathlib.lean`,
under `open CategoryTheory` (`𝟙` and `≫` are scoped to that namespace, like the
book's notations are to `Ch16`).

The two definitions describe the same notion, and every category of the book's
class can be translated into Mathlib's. The translation, in
`code/lean/Book/Ch16/Bridge.lean`, shows exactly what the change of order does:

```lean
{{#include ../../code/lean/Book/Ch16/Bridge.lean:bridge}}
```

```lean
{{#include ../../code/lean/Book/Ch16/Bridge.lean:bridge_use}}
```

Because the order of composition is reversed, Mathlib's left unit law is the
book's right unit law and vice versa, while associativity survives unchanged.
`.{0}` fixes Mathlib's morphism universe to `Type`, which is where the book's
`Hom` lives, and `abbrev` marks the definition as reducible, as Lean recommends
for definitions whose type is a class.

> [!WARNING]
> Mathlib's `⟶` is *global* notation, while the book's is scoped to `Ch16`.
> Inside `namespace Ch16` (or after `open Ch16`) in a file that imports Mathlib's
> category theory, `X ⟶ Y` is therefore ambiguous and Lean reports an error.
> That is why `InMathlib.lean` does not import the book's class, and why
> `Bridge.lean` never writes the arrow. In your own files, keep the two worlds
> apart, or write the book's arrow as `Ch16.Category.Hom X Y`.

### `Type u` as a category

Mathlib makes `Type u` a category for every universe `u`, and here it made a
choice that differs from ours: **a morphism `X ⟶ Y` in `Type u` is not literally
a function**, but a one-field structure (`TypeCat.Hom`) that wraps one. The
wrapper keeps Lean from confusing morphisms with functions during automation,
which matters in a library of this size. You build a morphism from a function
with `↾f`, and you apply a morphism to an element as if it were a
function, through a coercion:

```lean
{{#include ../../code/lean/Book/Ch16/InMathlib.lean:mathlib_types}}
```

The last example is the simp lemma that makes this convenient:
`(f ≫ g) x = g (f x)`, the diagrammatic order turned into ordinary application.

### Preorders, monos and epis

Every preorder is a category in Mathlib too, with `homOfLE` turning a proof of
`x ≤ y` into a morphism and `leOfHom` going back. Thinness is the statement that
the type of morphisms is a `Subsingleton` (it has at most one element):

```lean
{{#include ../../code/lean/Book/Ch16/InMathlib.lean:mathlib_preorder}}
```

Mono and epi are classes (`Mono f`, `Epi f`) and the theorems we proved by hand
are in the library:

```lean
{{#include ../../code/lean/Book/Ch16/InMathlib.lean:mathlib_mono}}
```

### Products through `Limits`

Mathlib does not define products on their own. Terminal objects, products,
equalizers, pullbacks and many other universal constructions are all special
cases of one notion, a **limit**, whose definition needs functors and natural
transformations (Chapters 17 and 18). Products are limits of a diagram with two
objects and no arrows: a discrete category with two objects, which is why we
said those trivial-looking categories are building blocks. You can use the
library without knowing the general definition:

```lean
{{#include ../../code/lean/Book/Ch16/InMathlib.lean:mathlib_products}}
```

- `HasBinaryProducts C` says that every two objects of `C` have a chosen
  product, written `A ⨯ B` (a special symbol, typed `\X`, not the `×` of pair
  types). `prod.lift`, `prod.fst` and `prod.snd` are our `lift`, `fst` and
  `snd`, and `prod.lift_fst` and `prod.lift_snd` are the two triangles.
- Uniqueness takes the form `prod.hom_ext`: two morphisms into a product are
  equal if their projections are. Our `uniq` follows, as the second example
  shows: `apply prod.hom_ext` leaves the two projection equations, and `simp`
  closes each with the hypothesis and `prod.lift_fst` (or `prod.lift_snd`).
- In `Type`, `Types.binaryProductLimit` is our `pairIsProduct`, so the
  library's `X ⨯ Y` is isomorphic to `X × Y`. That isomorphism is
  `noncomputable`: the library's product is chosen by a non-constructive
  principle, so Lean has no program to run.
- `Types.isTerminalPUnit` says that `PUnit` (a `Unit` that exists in every
  universe) is terminal.

## Common confusions

**"The objects are sets and the morphisms are functions."** Only in categories
like the category of types. In a preorder the morphisms are proofs, in a monoid
they are elements, in a free category they are paths.

**"$g \circ f$ means first $g$."** It means first $f$: $(g \circ f)(x) = g(f(x))$.
The book's `g ⊚ f` and `comp g f` follow this convention. Mathlib's `f ≫ g` uses
the opposite, diagrammatic order. When you move between the two, the unit laws
swap names.

**"A product is the pair type."** A product is *anything* with the universal
property: `min`, `∧`, pairs. Within one category all products of the same two
objects are isomorphic, in a unique way that respects the projections, so it
does not matter which one you pick.

**"Rust's `(A, B)` is a categorical product."** Only if you can duplicate the
input of the pairing: the diagonal $A \to A \times A$ needs `Clone`. For types
that cannot be copied, `(A, B)` is a weaker structure that Chapter 19 calls a
*monoidal* product. The coproduct, `enum`, has no such problem.

**"Mono means injective, and mono plus epi means isomorphism."** True in the
category of types, false in general: in `ℕ` with `≤`, every arrow is mono and
epi, and only the identities are isomorphisms.


## Summary

- A category has objects, morphisms, identities and an associative composition
  with the identities as units; composition is only defined when arrows meet.
- The book's `Ch16.Category` class states the laws as fields, so every instance
  carries proofs; its `Hom` lives in `Type`, a simplification of Mathlib's
  universe-polymorphic version.
- Types and functions, preorders (thin categories), monoids (one object),
  discrete categories (only identities) and free categories (paths, such as the
  traces of a protocol) are all categories. Rust can represent them as runtime
  data and test the laws; Lean checks composability by types and proves the laws.
- A commutative diagram is an equation between composites: a property test with
  a proof.
- Inverses are unique. In the category of types, monos are the injective and
  epis the surjective functions, but mono and epi together do not make an
  isomorphism in general.
- Terminal and initial objects, products and coproducts are defined by universal
  properties, like interface specifications, and are unique up to unique
  isomorphism. In Lean's types they are `Unit`, `Empty`, pairs and sums; in `ℕ`,
  `0`, `min` and `max`; in `Prop`, `True`, `False`, `∧` and `∨`.
- The opposite category reverses all arrows, and duality turns every definition
  and theorem into its mirror image for free.
- Rust's pairing of functions needs `Clone` (the diagonal is contraction), and
  side effects break the uniqueness of maps into `()`.
- Mathlib writes `X ⟶ Y`, `𝟙 X` and `f ≫ g` (diagrammatic order), wraps the
  morphisms of `Type u` in a structure, and defines products as limits.

## Exercises

1. Prove in Lean that every isomorphism is a monomorphism,
   `theorem iso_mono (i : a ≅ b) : Mono i.hom`, and then that it is an
   epimorphism.
   *Hint:* given `i.hom ⊚ g = i.hom ⊚ h`, compose both sides with `i.inv` on the
   left: a `calc` chain from `g` to `Category.id a ⊚ g` to
   `(i.inv ⊚ i.hom) ⊚ g`, regrouped with `Category.assoc`.

2. Prove that coproducts are unique up to isomorphism, once directly (copying
   `IsProduct.iso`) and once by duality, through a definition
   `IsCoproduct.op : IsCoproduct inl inr → IsProduct ...` in the opposite
   category.
   *Hint:* the fields of the product in `Op Obj` are those of the coproduct,
   unchanged (`lift f g := h.desc f g`, and so on); named arguments such as
   `(a := (⟨a⟩ : Op Obj))` tell Lean which objects you mean.

3. Define in Lean the category `FinObj` whose objects are natural numbers
   (wrapped in a structure) and whose morphisms from `m` to `n` are the functions
   `Fin m → Fin n` (where `Fin n` is the type of numbers below `n`). Then show
   that `⟨0⟩` is initial and `⟨1⟩` is terminal.
   *Hint:* the instance is a copy of `typeCategory`, with every law `rfl`. For
   the universal properties, `Fin 0` has no elements (`nomatch` or
   `Fin.elim0`) and every element of `Fin 1` is `0` (`Fin.ext` and `omega`, or
   `Subsingleton.elim`).

4. In Rust, implement the `Category` trait for **matrices**: objects are
   dimensions (`usize`), a morphism $n \to m$ is an $m \times n$ matrix of `i64`,
   composition is matrix multiplication, identities are identity matrices. Check
   the laws with `check_laws` on a few small matrices.
   *Hint:* store each matrix with its dimensions. For $f : n \to m$ and
   $g : m \to k$, $g \circ f$ is the product $G F$, a $k \times n$ matrix; return
   `None` when the inner dimensions differ.

5. In the preorder of natural numbers ordered by divisibility (now including
   0), what are the product and the coproduct of $a$ and $b$? Which number is
   initial, and which is terminal? Compare with the table in "Putting it
   together".
   *Hint:* translate "a morphism $x \to a$" into "$x$ divides $a$" and read the
   universal property aloud. Every number divides 0.

6. The Rust function `pair` requires `X: Clone`. Write a version `pair_ref`
   whose functions take `&X`, so that no bound is needed, and explain why it
   does not contradict the claim that the diagonal needs a copy.
   *Hint:* what is duplicated now? A shared reference `&X` is `Copy`, whatever
   `X` is (Chapters 23 and 26 explain why).
