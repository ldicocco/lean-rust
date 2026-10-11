# The Affine Lambda Calculus

Chapter 21 took the structural rules away from logic one at a time and looked at
what was left. Without contraction, an assumption stops being a fact that can be
quoted as often as you like and becomes a *resource* that is spent when it is
used. The logic that keeps weakening but drops contraction is **affine logic**:
every assumption is used at most once.

This chapter does for affine logic what Chapter 8 did for intuitionistic logic.
It builds the programming language whose type system *is* the logic: the
**affine λ-calculus**, $\lambda^{\mathsf{aff}}$. Its typing rules fit on one page,
and they are the formal content of the first half of the claim that "Rust's
ownership is based on affine types": moves, the error "use of moved value"
(E0382), partial moves, closures that can be called only once. There are no
references and no lifetimes here; those are Part VI. This chapter is pure move
semantics.

We will write every rule down, build derivations by hand and in Lean, and prove
the theorem that makes the calculus affine: in a well-typed term, every variable
is used at most once. Then we turn the rules into an algorithm, prove it sound
and complete in Lean, implement it in Rust as the `affine` crate, and put the
crate's error messages side by side with rustc's.

**In this chapter you will learn:**

- the syntax and typing rules of $\lambda^{\mathsf{aff}}$, and how *splitting* the
  context replaces *sharing* it in rules with two subterms;
- how to build derivations, and why swapping a pair has one while duplicating a
  value has none;
- why a pair of type $\tau \otimes \sigma$ is taken apart with `let` and not with
  projections, and how Rust's partial moves refine this one place at a time;
- the usage theorem and its complete proof in Lean;
- the metatheory around it: weakening is admissible, contraction is not, and
  substitution and preservation hold;
- how to check the rules with input and output contexts ("leftovers"), with a
  Lean proof that this algorithm is sound and complete;
- how the `affine` crate reports errors modeled on E0382, and where it agrees and
  disagrees with rustc.

## From affine logic to a programming language

Here is what we need from earlier chapters. Chapter 6 introduced the three
structural rules: exchange (the order of assumptions does not matter), weakening
(an assumption may go unused) and contraction (an assumption may be used twice).
Chapter 21 arranged the logics that drop some of them in a lattice: **linear**
logic drops weakening and contraction (every assumption used exactly once),
**affine** logic drops only contraction (at most once).

Chapter 21 also found that, once contraction is gone, the familiar connectives
split in two. Conjunction becomes $A \otimes B$ ("tensor", I have both, and they
were paid for with *disjoint* resources) and $A \mathbin{\&} B$ ("with", I can
give you either one, your choice, both built from the *same* resources).
Disjunction becomes $A \oplus B$, and implication becomes $A \multimap B$
("lollipop", a function that uses its argument at most once). Girard's coin is
the standard illustration: with one coin you can have a coffee *or* a tea
($\mathsf{Coffee} \mathbin{\&} \mathsf{Tea}$), but not a coffee *and* a tea
($\mathsf{Coffee} \otimes \mathsf{Tea}$).

The difference between the two conjunctions lives in one operation on contexts,
**context splitting**. The introduction rule of $\otimes$ divides the
assumptions between its two premises, $\Gamma = \Gamma_1 \uplus \Gamma_2$, so that
each assumption goes to one premise only. The introduction rule of
$\mathbin{\&}$ gives the *whole* context to both premises, which is safe because
only one of the two will ever be used.

Chapter 10 showed how to read a natural-deduction system as a programming
language: propositions become types, proofs become terms, assumptions become
variables, and each rule becomes a typing rule that says how to build a term.
Applied to the intuitionistic logic of Chapter 4, the recipe gives the simply
typed λ-calculus of Chapter 8. Applied to affine logic, it gives
$\lambda^{\mathsf{aff}}$.

> [!NOTE]
> $\lambda^{\mathsf{aff}}$ is a model of a fragment of Rust: values that are
> moved, never borrowed. When we say "this rule is the move checker", we mean
> that the rule rejects the same programs that rustc rejects with E0382, for the
> same reason, on the programs that both of them understand. How rustc actually
> implements the check (a dataflow analysis on a control-flow graph) is the
> subject of Chapter 29.

## Syntax

### Types

$$
\tau, \sigma, \rho \;::=\; b \;\mid\; \mathbf{1} \;\mid\; \tau \multimap \sigma \;\mid\; \tau \otimes \sigma \;\mid\; \tau \mathbin{\&} \sigma \;\mid\; \tau \oplus \sigma
$$

| Type | Read as | Rust $\approx$ | Logic |
|---|---|---|---|
| $b$ | base type | `String`, `File`, `Conn` | atom |
| $\mathbf{1}$ | unit | `()` | unit of $\otimes$ |
| $\tau \multimap \sigma$ | affine function | `FnOnce(τ) -> σ` | linear implication |
| $\tau \otimes \sigma$ | pair | `(τ, σ)` | multiplicative "and" |
| $\tau \mathbin{\&} \sigma$ | offer of either | one value, two consuming methods | additive "and" |
| $\tau \oplus \sigma$ | sum | an `enum` with two variants | additive "or" |

A base type $b$ is an opaque resource: the calculus has no operations on it and
no constants of that type. Values of base type enter a program through its
context, as the parameters of a Rust function do, and the calculus only describes
how they are passed around.

### Terms

$$
e \;::=\; x \;\mid\; \lambda x{:}\tau.\,e \;\mid\; e_1\,e_2 \;\mid\; () \;\mid\; (e_1, e_2) \;\mid\; \mathtt{let}\ (x, y) = e_1\ \mathtt{in}\ e_2 \;\mid\; \mathtt{let}\ x = e_1\ \mathtt{in}\ e_2
$$

$$
\;\mid\; \langle e_1, e_2 \rangle \;\mid\; \mathsf{fst}\,e \;\mid\; \mathsf{snd}\,e \;\mid\; \mathsf{inl}\,e \;\mid\; \mathsf{inr}\,e \;\mid\; \mathtt{case}\ e\ \{x.\,e_1 \mid y.\,e_2\}
$$

Most of these are familiar from Chapter 8; the differences are in what the typing
rules will allow.

- $\lambda x{:}\tau.\,e$ is a function that may use its argument at most once. It
  also *takes* every variable of the context that its body uses, the way a Rust
  closure takes ownership of what its body consumes. A function is itself a
  resource: a value of type $\tau \multimap \sigma$ can be called once, like an
  `FnOnce`.
- $(e_1, e_2)$ builds a pair of type $\tau \otimes \sigma$, and
  $\mathtt{let}\ (x, y) = e_1\ \mathtt{in}\ e_2$ takes one apart, binding *both*
  components at once. There are no projections $\mathsf{fst}$ and $\mathsf{snd}$
  for $\otimes$; a section below explains why.
- $\langle e_1, e_2 \rangle$ is an offer of type $\tau \mathbin{\&} \sigma$:
  two computations, of which the consumer will run exactly one, chosen with
  $\mathsf{fst}$ or $\mathsf{snd}$. The components are not evaluated when the
  offer is built.
- $\mathsf{inl}\,e$ and $\mathsf{inr}\,e$ inject into a sum, and
  $\mathtt{case}\ e\ \{x.\,e_1 \mid y.\,e_2\}$ inspects one: if $e$ is
  $\mathsf{inl}\,v$ it runs $e_1$ with $x$ bound to $v$, otherwise $e_2$ with $y$
  bound to $v$. It is Rust's `match` on a two-variant `enum`.
- $\mathtt{let}\ x = e_1\ \mathtt{in}\ e_2$ is Rust's `let x = e1; e2`. It could be
  defined as $(\lambda x{:}\tau.\,e_2)\,e_1$, but it is more convenient as a
  construct of its own.

Two things are missing on purpose. There is no construct for throwing a value
away: discarding is built into the typing rules, as we will see, and Chapter 24
adds an explicit $\mathtt{drop}\ x;\ e$ when it needs to talk about the moment of
discarding. And there is no recursion, so every program terminates; general
recursion would not change anything in this chapter's theorems (Exercise 6
asks you to check one of them).

### In Lean

The Lean development of this chapter lives in four files in
`code/lean/Book/Ch22/`: `Syntax.lean`, `Typing.lean`, `Usage.lean` and
`Checker.lean`, each importing the previous one. The types are an ordinary
inductive type:

```lean
{{#include ../../code/lean/Book/Ch22/Syntax.lean:ty}}
```

The additive pair is called `amp` (for the ampersand) because `with` is a
keyword in Lean. A few notations make the types readable:

```lean
{{#include ../../code/lean/Book/Ch22/Syntax.lean:notation}}
```

The numbers are precedences, and `infixr` makes $\multimap$ associate to the right
as $\to$ does. The keyword `scoped` makes each notation active only inside the
namespace `Ch22` (or where that namespace is opened), so that it does not leak
into other chapters, where $\otimes$ means something else. The symbol `⊕` is
also Lean's notation for the sum of two *Lean* types; Lean chooses between the
two meanings by the types of the arguments, and here they are always `Ty`s.

For the terms, we use de Bruijn indices, as Chapter 7 introduced them and
Chapter 9 used them for its proof of type safety: a variable is the number of
binders between it and its binder. Every binding construct says how many
variables it binds:

```lean
{{#include ../../code/lean/Book/Ch22/Syntax.lean:term}}
```

Inside the body of a `letPair`, the second component $y$ is `var 0` and the
first component $x$ is `var 1`: the innermost binder gets index 0, and we treat
$y$ as bound after $x$. The injections carry the *other* summand as an
annotation, so that every term has at most one type, which keeps the checker
later in the chapter simple. Here are three of the chapter's examples, written
with this convention:

```lean
{{#include ../../code/lean/Book/Ch22/Syntax.lean:examples}}
```

The function at the heart of the chapter counts how many times a term uses a
variable:

```lean
{{#include ../../code/lean/Book/Ch22/Syntax.lean:uses}}
```

Under one binder the same free variable has a larger index, so the count goes
from `i` to `i + 1` (to `i + 2` under `letPair`). Where two subterms both run,
as in an application or a pair, the counts add up. Where only one of two
alternatives will ever run, in an offer and in the branches of a `case`, the
count is the *maximum* of the two. That is the counting convention that the
usage theorem needs, and we will come back to it.

```lean
{{#include ../../code/lean/Book/Ch22/Syntax.lean:uses_eval}}
```

Finally, `Syntax.lean` gives `Ty` a printer, so that Lean shows types the way
this chapter writes them:

```lean
{{#include ../../code/lean/Book/Ch22/Syntax.lean:show_ty}}
```

## Contexts and splitting

A context is a list of distinct variables with their types,
$\Gamma = x_1 : \tau_1, \dots, x_n : \tau_n$. We keep the exchange rule, as
every substructural logic of interest to Rust does, so the order of a context
does not matter.

The splitting judgment $\Gamma = \Gamma_1 \uplus \Gamma_2$ says that $\Gamma$ is
divided between $\Gamma_1$ and $\Gamma_2$. It is defined by three rules that
walk through the context and send each variable left or right:

$$
\dfrac{}{\cdot = \cdot \uplus \cdot}\;\textsf{S-Empty}
\qquad
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2}{\Gamma, x : \tau = (\Gamma_1, x : \tau) \uplus \Gamma_2}\;\textsf{S-Left}
\qquad
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2}{\Gamma, x : \tau = \Gamma_1 \uplus (\Gamma_2, x : \tau)}\;\textsf{S-Right}
$$

The dot $\cdot$ is the empty context. Every variable goes to exactly one side, so
a context with $n$ variables has $2^n$ splits. For $x : A, y : B$ there are four:
both left, $x$ left and $y$ right, $x$ right and $y$ left, both right. Chapter 23
will add a fourth rule, S-Both, that sends a variable to both sides when its type
is `Copy`; Chapter 28 uses all four.

### Contexts with holes

In Lean a context cannot simply be a list of types, because de Bruijn indices are
positions: if a split removed a variable from the list, every variable after it
would be renumbered, and a term would mean something else in each half of the
split. So a Lean context keeps every position and marks the variables that are
not available with a **hole**:

```lean
{{#include ../../code/lean/Book/Ch22/Typing.lean:ctx}}
```

```lean
{{#include ../../code/lean/Book/Ch22/Typing.lean:split}}
```

Rules `left` and `right` are S-Left and S-Right: an available variable goes to
one side and leaves a hole on the other. Rule `hole` says that a position that is
already a hole stays a hole on both sides. With holes, the three contexts of a
split always have the same length, and `var 3` means the same variable in all of
them. For example, `Split [some A, some B] [some A, none] [none, some B]` gives
variable 0 to the left and variable 1 to the right. The same idea will return in
the checker, where "a hole" will mean "already moved".

## The typing rules

The judgment $\Gamma \vdash e : \tau$ reads as before: in context $\Gamma$, the
term $e$ has type $\tau$. What is new is that the context is a supply of
resources, and the rules decide who gets them. Here are all the rules. A bound
variable is always assumed to be fresh (not already in the context), as in
Chapter 7.

$$
\dfrac{}{\Gamma, x : \tau \vdash x : \tau}\;\textsf{A-Var}
\qquad
\dfrac{}{\Gamma \vdash () : \mathbf{1}}\;\textsf{A-Unit}
$$

$$
\dfrac{\Gamma, x : \tau \vdash e : \sigma}{\Gamma \vdash \lambda x{:}\tau.\,e : \tau \multimap \sigma}\;\textsf{A-Abs}
\qquad
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2 \qquad \Gamma_1 \vdash e_1 : \tau \multimap \sigma \qquad \Gamma_2 \vdash e_2 : \tau}{\Gamma \vdash e_1\,e_2 : \sigma}\;\textsf{A-App}
$$

$$
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2 \qquad \Gamma_1 \vdash e_1 : \tau \qquad \Gamma_2 \vdash e_2 : \sigma}{\Gamma \vdash (e_1, e_2) : \tau \otimes \sigma}\;\textsf{A-Pair}
$$

$$
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2 \qquad \Gamma_1 \vdash e_1 : \tau \otimes \sigma \qquad \Gamma_2, x : \tau, y : \sigma \vdash e_2 : \rho}{\Gamma \vdash \mathtt{let}\ (x, y) = e_1\ \mathtt{in}\ e_2 : \rho}\;\textsf{A-LetPair}
$$

$$
\dfrac{\Gamma \vdash e_1 : \tau \qquad \Gamma \vdash e_2 : \sigma}{\Gamma \vdash \langle e_1, e_2 \rangle : \tau \mathbin{\&} \sigma}\;\textsf{A-With}
\qquad
\dfrac{\Gamma \vdash e : \tau \mathbin{\&} \sigma}{\Gamma \vdash \mathsf{fst}\,e : \tau}\;\textsf{A-Fst}
\qquad
\dfrac{\Gamma \vdash e : \tau \mathbin{\&} \sigma}{\Gamma \vdash \mathsf{snd}\,e : \sigma}\;\textsf{A-Snd}
$$

$$
\dfrac{\Gamma \vdash e : \tau}{\Gamma \vdash \mathsf{inl}\,e : \tau \oplus \sigma}\;\textsf{A-Inl}
\qquad
\dfrac{\Gamma \vdash e : \sigma}{\Gamma \vdash \mathsf{inr}\,e : \tau \oplus \sigma}\;\textsf{A-Inr}
$$

$$
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2 \qquad \Gamma_1 \vdash e : \tau \oplus \sigma \qquad \Gamma_2, x : \tau \vdash e_1 : \rho \qquad \Gamma_2, y : \sigma \vdash e_2 : \rho}{\Gamma \vdash \mathtt{case}\ e\ \{x.\,e_1 \mid y.\,e_2\} : \rho}\;\textsf{A-Case}
$$

$$
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2 \qquad \Gamma_1 \vdash e_1 : \tau \qquad \Gamma_2, x : \tau \vdash e_2 : \sigma}{\Gamma \vdash \mathtt{let}\ x = e_1\ \mathtt{in}\ e_2 : \sigma}\;\textsf{A-Let}
$$

Read aloud, with the Rust construct each rule models:

| Rule | In words | Rust $\approx$ |
|---|---|---|
| A-Var | a variable has its type; others may idle | using a variable by value moves it |
| A-Abs | the body may use the argument and anything else | a closure takes what its body uses |
| A-App | function and argument use disjoint variables | a call partitions what it moves |
| A-Pair | the components use disjoint variables | `(a, b)` moves `a` and `b` |
| A-LetPair | take a pair apart, getting both parts | `let (x, y) = p;` |
| A-With | both alternatives may use everything | a value with two `self` methods |
| A-Case | scrutinee and branches split; branches share | `match` arms |
| A-Let | the value and the rest split | `let x = e1; e2` |

### Three rules to stare at

**A-Var: where weakening lives.** The axiom allows an arbitrary $\Gamma$ next to
the variable, and A-Unit allows an arbitrary context too. Those extra variables
are not used. In a *linear* calculus the axiom would be

$$
\dfrac{}{x : \tau \vdash x : \tau}\;\textsf{L-Var}
$$

with nothing else in the context, and A-Unit would demand an empty context. That
one difference is the whole difference between an affine language and a language
in which every value must be consumed. Rust is on the affine side: a function
may ignore a parameter, and the value is then simply dropped at the end of the
function (Chapter 24 is about what "dropped" costs).

**A-App and A-Pair: splitting is the move checker.** To type $(e_1, e_2)$ you
must divide the variables in scope between the two components, and no variable
can go to both. When you write `f(a, b)` in Rust, the compiler must be able to
partition the owned values in scope between the argument positions; if both
arguments mention the same non-`Copy` variable, no partition exists, and you get
E0382. Every rule whose premises *both run* splits the context: A-App, A-Pair,
A-LetPair, A-Let, and A-Case between the scrutinee and the branches.

**A-With and A-Case: sharing because only one alternative runs.** In A-With both
premises have the same $\Gamma$, and in A-Case the two branches have the same
$\Gamma_2$. This is *not* contraction. An offer $\langle e_1, e_2 \rangle$ runs
only the alternative the consumer chooses, and a `case` runs only one branch, so
each resource is still consumed at most once *when the program runs*. Rust does
the same: the borrow checker checks each arm of a `match` against the same
starting state, so a value moved in one arm is not thereby moved in the other.

### In Lean

Each rule becomes a constructor of an inductive predicate, with the premises as
arguments and the conclusion as the result type:

```lean
{{#include ../../code/lean/Book/Ch22/Typing.lean:has_type}}
```

Rule `var` says that variable `x` has type `τ` when position `x` of the context
holds `some τ`. The notation `Γ[x]?` is Lean's indexing that returns an `Option`
(`none` when `x` is out of range), like Rust's `slice.get(x)`; we write
`some (some τ)` because the context entries are themselves options. Nothing is
said about the other positions: that is A-Var's weakening. The binding rules
extend the context at the front, with `some τ :: Γ`, because the innermost
variable has index 0. The implicit arguments in braces are the metavariables of
the rule, which Lean will infer whenever we use a constructor.

## Worked derivations

### Swap is typable

The function that swaps a pair uses each of its variables exactly once:

$$
\vdash \lambda p.\,\mathtt{let}\ (x, y) = p\ \mathtt{in}\ (y, x) : (\tau \otimes \sigma) \multimap (\sigma \otimes \tau)
$$

Read the derivation from the bottom. A-Abs puts $p$ in the context. A-LetPair
must split $p : \tau \otimes \sigma$ between the scrutinee and the body; the
scrutinee is $p$ itself, so $p$ goes left and the body gets the empty context,
extended with $x$ and $y$. Finally A-Pair splits $x : \tau, y : \sigma$ so that
$y$ goes to the first component and $x$ to the second. Writing the pair's
sub-derivation separately, and leaving the splits out of the trees:

$$
\mathcal{D} \;=\; \dfrac{\dfrac{}{y : \sigma \vdash y : \sigma}\;\textsf{A-Var} \qquad \dfrac{}{x : \tau \vdash x : \tau}\;\textsf{A-Var}}{x : \tau,\, y : \sigma \vdash (y, x) : \sigma \otimes \tau}\;\textsf{A-Pair}
$$

$$
\dfrac{\dfrac{\dfrac{}{p : \tau \otimes \sigma \vdash p : \tau \otimes \sigma}\;\textsf{A-Var} \qquad \mathcal{D}}{p : \tau \otimes \sigma \vdash \mathtt{let}\ (x, y) = p\ \mathtt{in}\ (y, x) : \sigma \otimes \tau}\;\textsf{A-LetPair}}{\vdash \lambda p.\,\mathtt{let}\ (x, y) = p\ \mathtt{in}\ (y, x) : (\tau \otimes \sigma) \multimap (\sigma \otimes \tau)}\;\textsf{A-Abs}
$$

with the splits $p : \tau \otimes \sigma = (p : \tau \otimes \sigma) \uplus \cdot$
and $x : \tau, y : \sigma = (y : \sigma) \uplus (x : \tau)$. In Lean the same
derivation is a term, one constructor per rule, and the splits appear as
arguments:

```lean
{{#include ../../code/lean/Book/Ch22/Typing.lean:swap_typed}}
```

The split for the `letPair` is `.left .nil`: the context has one entry, $p$, and
it goes left. The body's context is then `[some σ, some τ, none]`: $y$, $x$, and
the hole where $p$ was. The pair's split `.left (.right (.hole .nil))` reads
position by position: $y$ left, $x$ right, the hole stays a hole. Each leaf is
`.var rfl`: the premise `Γ[x]? = some (some τ)` is about a concrete list, so
Lean computes the lookup and `rfl` confirms it.

The `affine` crate, which we meet properly later in the chapter, prints the
derivation it finds for the same function written in Rust syntax. Each line is a
judgment with the context that the subterm actually used:

```text
{{#include ../../code/rust/output/ch22_affine_checker.txt:1:6}}
```

And Rust, of course, accepts the function. This chapter's Rust example,
`code/rust/examples/ch22_affine_in_rust.rs`, writes the terms of the calculus as
Rust functions:

```rust
{{#include ../../code/rust/examples/ch22_affine_in_rust.rs:swap}}
```

### Discarding is typable

The function $\lambda x.\,\lambda y.\,x$ ignores its second argument:

$$
\dfrac{\dfrac{\dfrac{}{x : \tau,\, y : \sigma \vdash x : \tau}\;\textsf{A-Var}}{x : \tau \vdash \lambda y.\,x : \sigma \multimap \tau}\;\textsf{A-Abs}}{\vdash \lambda x.\,\lambda y.\,x : \tau \multimap \sigma \multimap \tau}\;\textsf{A-Abs}
$$

The only interesting step is the top one: A-Var accepts the unused $y$ in the
context. In Lean the derivation is three constructors:

```lean
{{#include ../../code/lean/Book/Ch22/Typing.lean:discard_typed}}
```

In Rust, discarding is legal too, but it is not invisible. Here is the Rust
version, called with a `File` whose destructor writes to a log:

```rust
{{#include ../../code/rust/examples/ch22_affine_in_rust.rs:first}}
```

```text
{{#include ../../code/rust/output/ch22_affine_in_rust.txt:6:8}}
```

The file is closed *inside* `first`, before it returns: the discarded value was
dropped at the end of the function. The typing rule is the calculus's weakening;
the closing is what Chapter 24 calls weakening with a side effect.

### Duplication is not

Now try $\lambda x.\,(x, x)$ at type $\tau \multimap \tau \otimes \tau$. A-Abs
leaves us with $x : \tau \vdash (x, x) : \tau \otimes \tau$, and the only rule
for a pair is A-Pair, which needs a split $x : \tau = \Gamma_1 \uplus \Gamma_2$
with $\Gamma_1 \vdash x : \tau$ and $\Gamma_2 \vdash x : \tau$. The only rule
that concludes a variable is A-Var, which needs $x$ in the context. So $x$ would
have to be in both $\Gamma_1$ and $\Gamma_2$, and no split does that. There is no
derivation.

This argument proves more than it seems. The rule of contraction,

$$
\dfrac{\Gamma, x : \tau, y : \tau \vdash e : \rho}{\Gamma, z : \tau \vdash e[z/x, z/y] : \rho}\;\textsf{Contr}
$$

is **not admissible** in $\lambda^{\mathsf{aff}}$ (in the sense of Chapter 6: we
cannot add it without changing what is derivable). Its premise is derivable with
$e = (x, y)$, and its conclusion would be $z : \tau \vdash (z, z)$, which we just
showed is not. In Lean, the argument becomes a proof by inversion:

```lean
{{#include ../../code/lean/Book/Ch22/Typing.lean:no_dup}}
```

`cases h` asks which constructor could have produced a derivation of a pair; the
only candidate is `pair`, and Lean names its premises: the split `hs` and the two
derivations `h₁` and `h₂`. `cases h₁` and `cases h₂` do the same for the
variables: only `var` fits, which gives `g₁ : Γ₁[0]? = some (some _)` and the
same for `Γ₂`. Finally `cases hs` tries the constructors of `Split` for a
context whose first entry is `some τ`: `left` puts a hole at position 0 of
`Γ₂`, `right` puts one in `Γ₁`, and `hole` and `nil` do not fit at all. The
combinator `<;>` runs `simp at g₁ g₂` on every remaining case, and in each one
`simp` evaluates the lookup of the hole to `none`, turns the hypothesis into
`none = some _`, recognizes it as false and closes the goal.

Rust rejects the same function, and its message describes the failed split:

```rust
{{#include ../../code/rust/compile_fail/ch22_dup.rs:dup}}
```

```text
{{#include ../../code/rust/compile_fail/ch22_dup.stderr}}
```

"Value moved here" is the first component taking $s$; "value used here after
move" is the second component finding nothing left. The help at the end is a
glimpse of Chapter 23: `clone` is an *explicit* duplication, a term rather than a
structural rule.

## Sharing: offers and branches

The additive rules are where Girard's coin becomes a program. Suppose the
environment provides two functions, $\mathsf{coffee} : \mathsf{Coin} \multimap \mathsf{Coffee}$
and $\mathsf{tea} : \mathsf{Coin} \multimap \mathsf{Tea}$. (In the calculus a
function in the context would be a resource too, usable once; we treat these two
as constants, available in every context, the way a Rust program can call a
declared function as often as it likes. Chapter 23 explains why Rust may do
that.) Then

$$
c : \mathsf{Coin} \vdash \langle \mathsf{coffee}\,c,\ \mathsf{tea}\,c \rangle : \mathsf{Coffee} \mathbin{\&} \mathsf{Tea}
$$

is derivable by A-With, both alternatives using $c$, while

$$
c : \mathsf{Coin} \vdash (\mathsf{coffee}\,c,\ \mathsf{tea}\,c) : \mathsf{Coffee} \otimes \mathsf{Tea}
$$

is not, for the same reason as $(x, x)$. The crate's derivation of the offer
shows the coin in both premises:

```text
{{#include ../../code/rust/output/ch22_affine_checker.txt:10:15}}
```

Rust has no built-in $\mathbin{\&}$, but the idea is common in Rust APIs: a value
with several methods that take `self`. You may call any one of them, and calling
it uses the value up. The chapter's Rust example has a voucher, and a generic
version that stores the shared resources together with the two alternatives:

```rust
{{#include ../../code/rust/examples/ch22_affine_in_rust.rs:with}}
```

```rust
{{#include ../../code/rust/examples/ch22_affine_in_rust.rs:offers}}
```

Each voucher, each offer, is spent once. Spending one voucher twice is exactly
the $\otimes$ derivation that does not exist:

```rust
{{#include ../../code/rust/compile_fail/ch22_voucher_both.rs:voucher}}
```

```text
{{#include ../../code/rust/compile_fail/ch22_voucher_both.stderr}}
```

The note names the mechanism: `coffee` takes its receiver `self` by value, so
calling it is a move of `v`, like passing `v` to a function.

The two branches of a `case` share their context in the same way. Here is a
settlement that ships an order or refunds it, using the connection `c` in both
branches, in the crate's syntax and with the crate's derivation:

```text
{{#include ../../code/rust/output/ch22_affine_checker.txt:16:24}}
```

Each branch premise has `c` in its context. In Rust:

```rust
{{#include ../../code/rust/examples/ch22_affine_in_rust.rs:settle}}
```

This sharing is also why `uses` takes the maximum over branches. A variable that
appears once in each branch is used once on every run, so its count is
$\max(1, 1) = 1$, not $2$. The other side of the coin is that a variable moved
in *one* branch must be considered moved after the `case`, because the type
checker does not know which branch will run. The crate reports this case with
the move in the left arm:

```text
{{#include ../../code/rust/output/ch22_move_errors.txt:21:31}}
```

## Why `⊗` has no projections

In the simply typed λ-calculus a pair has two projections, and
$\lambda p.\,(\mathsf{snd}\,p, \mathsf{fst}\,p)$ swaps it. In
$\lambda^{\mathsf{aff}}$ that term is not typable: it uses $p$ twice. Projections
are the wrong eliminator for $\otimes$. A projection keeps one component and
silently abandons the other, the *orphaned* component; and two projections need
two uses of the pair.

In an affine calculus a projection can still be *defined*, because abandoning a
value is weakening, which we have:

```lean
{{#include ../../code/lean/Book/Ch22/Usage.lean:tensor_fst}}
```

`tfst e` is $\mathtt{let}\ (x, y) = e\ \mathtt{in}\ x$, with $y$ discarded, and
`tfst_typed` derives it for any well-typed pair (`Split.all_left` sends the whole
context to the scrutinee). But `no_both_projections` shows that the two
projections cannot both be applied to the same variable: the proof is one
application of the usage theorem of the next section, which finds variable 0
used twice. So the `let` that binds both components at once is not a
convenience. It is the only way to get both halves of a pair while using the pair
once.

Rust refines this. It tracks moves not per variable but per **place**: `p`,
`p.0` and `p.1` are different places, and moving out of `p.0` leaves `p.1` where
it was. That is why `swap_fields` above, written `(p.1, p.0)`, compiles. What
Rust does not allow is using `p` as a whole after one of its parts has been
moved:

```rust
{{#include ../../code/rust/compile_fail/ch22_partial_move.rs:split}}
```

```text
{{#include ../../code/rust/compile_fail/ch22_partial_move.stderr}}
```

After `let s = p.0;` the variable `p` is *partially moved*: a pair with a hole
in it. Its remaining part is still owned, and if nothing moves it, it is dropped
at the end of the scope (Chapter 24 describes how the compiler drops only the
fields that are still there). In the language of this chapter, rustc applies the
splitting discipline to places instead of variables, and the calculus's `let`
elimination is the special case in which every field of the pair is moved at the
same time.

## The usage theorem

We can now state and prove the theorem that the whole chapter has been preparing.

> **Theorem (usage).** If $\Gamma \vdash e : \tau$, then every variable of
> $\Gamma$ occurs free in $e$ at most once, counting occurrences in subterms that
> both run with $+$ and occurrences in the two alternatives of an offer or a
> `case` with $\max$. A variable that is not in $\Gamma$ does not occur free in
> $e$ at all.

The proof on paper is a short induction on the derivation. A-Var: the variable
of the axiom occurs once, every other variable zero times. A-Abs and the one-premise
rules: the induction hypothesis, for the same variable. The splitting rules: a
variable of $\Gamma$ goes to exactly one premise, where by induction it occurs at
most once, and it is absent from the other premise's context, where by induction
it does not occur; one plus zero is at most one. The sharing rules: by induction
the variable occurs at most once in each alternative, and the maximum of two
numbers at most one is at most one.

The Lean proof follows the paper proof, but it needs one idea to make "goes to
exactly one premise" precise. We count how many times each position of a context
*may* be used:

```lean
{{#include ../../code/lean/Book/Ch22/Usage.lean:avail}}
```

The key lemma says that a split hands out exactly what the context had:

```lean
{{#include ../../code/lean/Book/Ch22/Usage.lean:split_avail}}
```

It is proved by induction on the split, for every position `i`. At position 0,
each of the three constructors gives a different equation, $1 = 1 + 0$,
$1 = 0 + 1$ or $0 = 0 + 0$, and `simp` checks each by computing `avail`. At a
position `i + 1`, all three constructors behave the same: the head entries are
irrelevant, and the equation is the induction hypothesis at `i`. (`simpa using
ih i` simplifies both the goal and `ih i` with the same lemmas, among them
`avail_cons_succ`, which drops a head entry, and then closes the goal with the
simplified hypothesis.) The three cases share one proof thanks to the
`| left _ ih | right _ ih | hole _ ih =>` pattern, which handles several cases
with the same script.

Now the theorem itself. It is stated for every variable at once, with
`avail` playing the role of "is in $\Gamma$":

```lean
{{#include ../../code/lean/Book/Ch22/Usage.lean:usage}}
```

Each case is one line of the paper proof.

- **`var`**. The pattern `@var Γ x τ hx` names the implicit arguments of the
  constructor, so that we can talk about `x`. `by_cases hi : i = x` splits the
  proof in two. If `i = x`, then `subst` replaces `i` with `x` everywhere, and
  `simp` computes `uses x (.var x) = 1` and, with `hx`, `avail Γ x = 1`. If not,
  `uses i (.var x)` is 0, and $0 \le$ anything.
- **`unit`**. `uses i .unit = 0`.
- **`lam`**. Under the binder our variable has index `i + 1`, so we apply the
  induction hypothesis there; `simpa [uses]` turns `uses i (.lam τ e)` into
  `uses (i + 1) e` and `avail (some τ :: Γ) (i + 1)` into `avail Γ i`.
- **`app` and `pair`**. The heart of the proof. We collect three facts with
  `have`: the two induction hypotheses, one for each part of the split, and the
  splitting lemma $\mathit{avail}\ \Gamma\ i = \mathit{avail}\ \Gamma_1\ i + \mathit{avail}\ \Gamma_2\ i$. After
  `simp only [uses]` the goal is `uses i e₁ + uses i e₂ ≤ avail Γ i`, and
  `omega`, the decision procedure for linear arithmetic over the naturals, puts the
  three facts together.
- **`letPair`, `letIn` and `case`**. The same, except that the body's induction
  hypothesis is at index `i + 2` or `i + 1`, and `simp at h₂` first rewrites the
  extended context back to `Γ₂`.
- **`wpair`**. No split: both components have the whole context, and the goal
  is `max (uses i e₁) (uses i e₂) ≤ avail Γ i`. `omega` understands `max`, so the
  two induction hypotheses are enough. Had `uses` added the two counts instead,
  this case, and the corresponding part of `case`, would be false.
- **`fst`, `snd`, `inl`, `inr`**. The induction hypothesis, unchanged.

Two corollaries put the theorem in its familiar form:

```lean
{{#include ../../code/lean/Book/Ch22/Usage.lean:at_most_once}}
```

The first is "every variable is used at most once", since `avail` is never more
than 1. The second says that a hole, a variable that this part of the program
did not receive, is not used at all. And the impossibility proofs of the previous
section become one-liners. `dup` has no type in *any* context, and contraction
fails:

```lean
{{#include ../../code/lean/Book/Ch22/Usage.lean:dup_untypable}}
```

```lean
{{#include ../../code/lean/Book/Ch22/Usage.lean:contraction_fails}}
```

In `contraction_fails`, the first part is the premise of the contraction rule
(a derivation, with the split `.right (.left .nil)`: variable 0 goes right,
variable 1 left), and the second part shows that its conclusion has none.

The theorem is a statement about the program *text*. Its meaning for the program's
*runs* is that a resource bound to a variable reaches at most one place that will
be executed: the job of the next section is to say why that survives evaluation.
It is also a statement about *variables*. Rust counts uses of places, which is
finer, as we saw; and Rust's `Copy` types are exempt, which is Chapter 23.

## More metatheory

### Weakening is admissible

A-Var and A-Unit accept unused variables, but that alone does not show that
*every* derivation survives the addition of a variable to its context: the
splitting rules must decide where the new variable goes. The statement and
proof are about contexts in which some holes have been filled:

```lean
{{#include ../../code/lean/Book/Ch22/Typing.lean:wk}}
```

```lean
{{#include ../../code/lean/Book/Ch22/Typing.lean:split_wk}}
```

`Split.wk` makes the choice: the new variables go left. The proof walks along
the split; at a position where the old context had a hole and the new one has a
variable (`fill`), it uses `left` instead of `hole`. The `obtain` tactic takes
apart the existential of the induction hypothesis (as `let (a, b) = ...` does in
Rust), giving names to the witness and to the two facts about it. Weakening
itself is then an induction on the derivation:

```lean
{{#include ../../code/lean/Book/Ch22/Typing.lean:weaken}}
```

In each splitting rule, the bigger context is split with `hs.wk` and the
induction hypothesis is applied to the left premise. Putting the variables on
the right would work as well and give a different derivation: weakening is
admissible, but the derivation it produces is not unique. Weakening is not a
curiosity here; the checker's soundness proof below uses it in several places.

### Substitution and preservation

To say how programs *run*, we give $\lambda^{\mathsf{aff}}$ a call-by-value
semantics. The values are

$$
v \;::=\; \lambda x{:}\tau.\,e \;\mid\; () \;\mid\; (v_1, v_2) \;\mid\; \langle e_1, e_2 \rangle \;\mid\; \mathsf{inl}\,v \;\mid\; \mathsf{inr}\,v
$$

(an offer is a value with *unevaluated* components: nothing runs until the
consumer chooses), and the computation rules are

$$
(\lambda x{:}\tau.\,e)\,v \longrightarrow e[v/x]
\qquad
\mathtt{let}\ (x, y) = (v_1, v_2)\ \mathtt{in}\ e \longrightarrow e[v_1/x][v_2/y]
\qquad
\mathtt{let}\ x = v\ \mathtt{in}\ e \longrightarrow e[v/x]
$$

$$
\mathsf{fst}\,\langle e_1, e_2 \rangle \longrightarrow e_1
\qquad
\mathsf{snd}\,\langle e_1, e_2 \rangle \longrightarrow e_2
\qquad
\mathtt{case}\ \mathsf{inl}\,v\ \{x.\,e_1 \mid y.\,e_2\} \longrightarrow e_1[v/x]
\qquad
\mathtt{case}\ \mathsf{inr}\,v\ \{x.\,e_1 \mid y.\,e_2\} \longrightarrow e_2[v/y]
$$

together with rules that evaluate subterms from left to right, as in Chapter 9.
Notice the two rules for offers: the alternative that is not chosen is thrown
away without running. That is weakening at run time.

> **Lemma (substitution).** If $\Gamma, x : \sigma \vdash e : \tau$ and
> $\Delta \vdash v : \sigma$, where $\Gamma$ and $\Delta$ have no variable in
> common, then $\Gamma \uplus \Delta \vdash e[v/x] : \tau$.

The proof is by induction on the derivation of $e$, and its interesting cases are
exactly the two kinds of rules. In a **splitting** rule, $x$ went to exactly one
premise. Substitute there, using the induction hypothesis, and leave the other
premise alone: by the usage theorem, $x$ does not occur in it, so substitution
does not change it. The resources $\Delta$ of $v$ join the side that received
$x$. In a **sharing** rule ($\langle e_1, e_2 \rangle$ or the branches of a
`case`), $x$ may occur in both alternatives, and we substitute in both. The value
$v$ is then copied *syntactically*, but only one copy will ever run, and the
same derivation $\Delta \vdash v : \sigma$ serves in each alternative. This is
the precise sense in which sharing is not contraction.

> **Theorem (preservation).** If $\Gamma \vdash e : \tau$ and
> $e \longrightarrow e'$, then $\Gamma \vdash e' : \tau$.

Each computation rule replaces a destructor applied to a constructor by a
substitution, and the substitution lemma retypes the result, in the part of the
context that the redex used; weakening gives back the rest. The rules for
offers need only weakening. Progress (a closed well-typed term is a value or
steps) holds as in Chapter 9. Neither proof is mechanized in this chapter: they
have exactly the shape of Chapter 9's mechanized proofs, with the extra
bookkeeping of holes in the substitution lemma, and the usage theorem is the
part that is new.

Together, preservation and the usage theorem say what affinity means at run
time: at every step of a run, the program is well typed, so every resource
variable occurs in at most one place that can still execute.

## Checking with leftovers

The declarative rules say *what* a derivation looks like, but not how to find
one. Each splitting rule asks us to choose one of $2^n$ splits of the context, and
a type checker that tried them all would be hopeless. The way out is to stop
guessing. Give the *whole* context to the first subterm, and let it report what
it did not use: its **leftovers**. Give the leftovers to the second subterm, and
so on. A variable that the first subterm consumed is simply not there when the
second one looks for it.

This is an algorithmic judgment with an input and an output context,
$\Gamma \vdash e : \tau \dashv \Delta$, read "with $\Gamma$ available, $e$ has
type $\tau$ and leaves $\Delta$". Writing $\Gamma - x$ for $\Gamma$ with $x$
marked as used, here are four of its rules:

$$
\dfrac{(x : \tau) \in \Gamma}{\Gamma \vdash x : \tau \dashv \Gamma - x}
\qquad
\dfrac{\Gamma \vdash e_1 : \tau \dashv \Delta_1 \qquad \Delta_1 \vdash e_2 : \sigma \dashv \Delta_2}{\Gamma \vdash (e_1, e_2) : \tau \otimes \sigma \dashv \Delta_2}
$$

$$
\dfrac{\Gamma \vdash e_1 : \tau \dashv \Delta_1 \qquad \Gamma \vdash e_2 : \sigma \dashv \Delta_2}{\Gamma \vdash \langle e_1, e_2 \rangle : \tau \mathbin{\&} \sigma \dashv \Delta_1 \sqcap \Delta_2}
\qquad
\dfrac{\Gamma, x : \tau \vdash e : \sigma \dashv \Delta}{\Gamma \vdash \lambda x{:}\tau.\,e : \tau \multimap \sigma \dashv \Delta - x}
$$

The variable rule consumes. The pair *threads* the context: the output of $e_1$
is the input of $e_2$. The offer *forks* it: both alternatives start from
$\Gamma$, and what remains afterwards is the **meet** $\Delta_1 \sqcap \Delta_2$,
the variables that neither alternative used. The abstraction removes its
parameter from the leftovers, whether the body used it or not. The other rules
follow the same two patterns, threading for the splitting rules and forking for
the sharing ones.

![Checking with leftovers. Above, a pair threads the context: the first component consumes c and s, and the second receives only t. Below, an offer forks it: both alternatives start from the same context, and only what neither consumed is left.](../images/ch22-leftovers.svg)

### The checker in Lean

With contexts with holes, "marked as used" is "turned into a hole":

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:take}}
```

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:meet}}
```

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:infer}}
```

`infer` is a direct transcription of the algorithmic rules, in the `Option`
monad written out by hand: every `match` on a recursive call either continues
with the leftovers or gives up with `none`. A rule that needs a particular kind
of type, such as `app` needing a function, matches on the type's constructor.
The pattern `_ :: Δ` in `lam` drops the parameter's entry from the leftovers,
consumed or not. And we can run it:

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:infer_eval}}
```

### Soundness

An algorithm is only as good as its relation to the rules. The first half is
**soundness**: whatever the checker accepts has a derivation, and the part of the
context that the checker consumed is exactly the part the derivation uses.

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:infer_sound}}
```

The proof is by induction on the term, and it needs three facts about splits.
The first is that two splits in a row are one split:

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:split_assoc}}
```

This is what the threading rules need. Take the `app` case. Unfolding `infer`
with `simp only [infer] at h` turns the hypothesis into nested `match`
expressions, and each `split at h` considers the cases of one `match`: either
the recursive call succeeded, with values that `rename_i` gives names to, or it
failed, and then `h` says `none = some _` and `simp at h` closes the case. In
the successful case, the induction hypotheses give a split of $\Gamma$ into
$U_1$ (used by $e_1$) and $\Delta_1$, and a split of $\Delta_1$ into $U_2$ (used
by $e_2$) and $\Delta_2$. `Split.assoc` combines them into a split of $\Gamma$
into $U$ and $\Delta_2$ together with a split of $U$ into $U_1$ and $U_2$, which
is exactly the premise of rule `app`.

The second fact is for the forking rules. Two alternatives that start from the
same context use two parts of it; together they use the union, which splits off
the meet of the leftovers, and each alternative's part can be weakened to the
union:

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:split_meet}}
```

In the `wpair` case, the two derivations are weakened to that common context,
and rule `wpair` applies. This is where weakening becomes essential: the
declarative rule wants both alternatives typed in *the same* context, while the
checker found two different ones. The third fact, `Split.uncons`, handles
binders: when the body of a `lam` or `let` was checked with the bound variable in
front, the split of the extended context gives a split of the original one, and
the bound variable, used or not, can be put back by weakening. The `case`
rule uses all three facts.

Two corollaries close the circle with the previous sections:

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:infer_sound_cor}}
```

### Completeness

The second half is **completeness**: the checker never rejects a typable term.
For this we need to know exactly what the checker leaves behind. It removes
precisely the variables that the term uses:

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:consumed}}
```

The delicate point is threading. When `app` checks $e_2$ with the leftovers of
$e_1$, everything $e_2$ needs must still be there. It is, and the reason is the
usage theorem: $e_1$ uses only variables that its own part of the split
offered, so the variables of $e_2$'s part are untouched:

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:wk_consumed}}
```

The hypothesis `∀ i, f i ≤ avail U₁ i` is the usage theorem for $e_1$. With that
lemma, completeness is an induction on the derivation in which each case unfolds
`infer`, rewrites the recursive calls with the induction hypotheses, and checks
that the leftovers have the promised form:

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:infer_complete}}
```

Most cases end with `rfl` once `simp only` has rewritten the calls, because the
leftovers agree by definition. The `case` case needs one extra step: the
leftovers come out as $\max(u + v_1, u + v_2)$ and the specification says
$u + \max(v_1, v_2)$, which are equal but not by definition. `congr 2` and
`apply congrArg` reduce the goal to the equality of the two counting functions,
`funext` to their equality at every `i`, and `omega` proves it. Soundness and
completeness together say that the checker *decides* the typing relation:

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:decides}}
```

## The `affine` crate

The crate `code/rust/crates/affine` implements the same algorithm for a
language that looks like Rust, so that its programs and errors can be compared
with real ones. A program is a list of functions. Functions without a body are
provided by the environment, and calling a declared function uses its arguments
but not the function itself (it is a constant, like a Rust `fn` item):

| $\lambda^{\mathsf{aff}}$ | `affine` crate |
|---|---|
| $\tau \otimes \sigma$, $\tau \multimap \sigma$ | `(T, U)`, `FnOnce(T) -> U` |
| $\tau \mathbin{\&} \sigma$, $\tau \oplus \sigma$ | `With<T, U>`, `Either<T, U>` |
| $\mathtt{let}\ (x, y) = e_1\ \mathtt{in}\ e_2$ | `let (x, y) = e1; e2` |
| $\langle e_1, e_2 \rangle$, $\mathsf{fst}\,e$, $\mathsf{snd}\,e$ | `with(e1, e2)`, `e.fst`, `e.snd` |
| $\mathtt{case}\ e\ \{x.\,e_1 \mid y.\,e_2\}$ | `match e { Left(x) => e1, Right(y) => e2 }` |

A λ-abstraction $\lambda x{:}\tau.\,e$ is written as a closure, `|x: T| e`.
The crate also has what $\lambda^{\mathsf{aff}}$ deliberately lacks and Rust
has: projections `p.0` and `r.field` on places, with per-place move tracking,
structs, and (for Chapter 23) `Copy`, `.clone()` and `Rc`. It consists of a
parser, the checker (`check.rs`), the diagnostics (`diagnostic.rs`), and
derivation trees (`derivation.rs`).

### Contexts that remember moves

The crate's context is a stack of bindings, each recording where it was declared
and every move out of it:

```rust
{{#include ../../code/rust/crates/affine/src/check.rs:binding}}
```

A binding with a move whose path is empty is the crate's version of Lean's hole.
Unlike a hole, it remembers *where* the value went, which is what the error
message needs. The checker's main function has the shape of the algorithmic
judgment $\Gamma \vdash e : \tau \dashv \Delta$, and its Rust signature is itself
affine: it takes the context by value and gives back the leftovers.

```rust
{{#include ../../code/rust/crates/affine/src/check.rs:infer}}
```

The threading rule is two calls in a row, the second one receiving the first
one's output:

```rust
{{#include ../../code/rust/crates/affine/src/check.rs:pair}}
```

and the forking rule clones the context, the only place where the checker does
so, and merges the leftovers:

```rust
{{#include ../../code/rust/crates/affine/src/check.rs:with}}
```

```rust
{{#include ../../code/rust/crates/affine/src/check.rs:merge}}
```

Every error E0382 comes from one function, the use of a place:

```rust
{{#include ../../code/rust/crates/affine/src/check.rs:use_place}}
```

A use is an error if the same place, or a place that contains it, has been
moved (`path.starts_with(&m.path)`), or if a part of it has been moved. Otherwise
the use records a move, unless the type is `Copy`, which in this chapter's
discipline nothing is. A use inside a closure body of a variable declared outside
the closure is recorded as a move *into the closure*, at the closure's head,
which is what A-Abs says: the closure takes what its body uses.

Each call of `infer` also builds a node of a derivation, whose context is the
set of variables that the subterm used: the part of the input context that is
not in the output. That is the context $U$ of the soundness theorem, and it is
how the crate prints derivations of the declarative system from a run of the
algorithmic one:

```rust
{{#include ../../code/rust/crates/affine/src/derivation.rs:derivation}}
```

The example `crates/affine/examples/ch22_affine_checker.rs` checks the programs
of `crates/affine/examples/programs/ch22_accepted.aff`:

```text
{{#include ../../code/rust/crates/affine/examples/programs/ch22_accepted.aff}}
```

and prints the derivations; we have seen most of them already. Two lines are new.
After `first`, the crate notes that `f` was discarded without use, the weakening
of A-Var. And `later` shows A-Abs: the closure's context holds the two captured
variables, and the premise adds the parameter `u`, unused:

```text
{{#include ../../code/rust/output/ch22_affine_checker.txt:7:9}}
```

```text
{{#include ../../code/rust/output/ch22_affine_checker.txt:25:29}}
```

### Side by side with rustc

The example `ch22_move_errors.rs` runs the checker on six programs that it
rejects. The first is `dup`:

```text
{{#include ../../code/rust/output/ch22_move_errors.txt:1:9}}
```

Compare it with rustc's output for the same function earlier in the chapter. The
labels are the same, in the same places: the declaration that explains why the
value moves, the move, and the use after the move. rustc adds a suggestion to
clone. The coin is the crate's version of the voucher:

```text
{{#include ../../code/rust/output/ch22_move_errors.txt:11:19}}
```

The partial move, with the crate's per-place tracking, matches rustc's message
word for word, note included:

```text
{{#include ../../code/rust/output/ch22_move_errors.txt:33:41}}
```

A closure that uses a variable takes it:

```text
{{#include ../../code/rust/output/ch22_move_errors.txt:43:53}}
```

and rustc says the same about the closure `|| send(c, msg)`:

```rust
{{#include ../../code/rust/compile_fail/ch22_closure_capture.rs:capture}}
```

```text
{{#include ../../code/rust/compile_fail/ch22_closure_capture.stderr}}
```

The first eleven lines are the same diagnosis; rustc then explains two ways out
(borrow instead of owning, or clone). Finally, a function of type
$\tau \multimap \sigma$ is a resource, so calling it twice is a second use of it,
as rustc says for an `FnOnce` (Chapter 8 showed rustc's version of this error):

```text
{{#include ../../code/rust/output/ch22_move_errors.txt:55:63}}
```

The crate and rustc agree on these programs, but they get there differently.
The crate follows the syntax tree, rule by rule; rustc lowers the function to a
control-flow graph and runs a dataflow analysis over it (Chapter 29), which is
how it handles loops, early returns and conditional moves that the calculus does
not have. rustc also infers more types than the crate (where the crate needs
`let x: Either<A, B> = Left(a);`, rustc infers the type from later uses), and its
closures capture by reference whenever the body only reads a variable, which is
borrowing, Part VI. On the affine fragment, though, the two agree on which
programs to reject and on why.

## Putting it together: an upload

Here is a small program that does something a real service does: read a file,
send its contents over a connection, close the file, and keep the connection for
later. It is followed by two buggy versions:

```text
{{#include ../../code/rust/crates/affine/examples/programs/ch22_upload.aff}}
```

The crate accepts `upload`. Read its derivation from the top, watching the
contexts shrink:

```text
{{#include ../../code/rust/output/ch22_affine_checker.txt:31:42}}
```

The whole body uses both parameters. A-LetPair splits them: `file` goes to
`read_all(file)`, and `conn` to the rest, which also receives the two new
variables `data` and `opened`. The next `let` splits again: `conn` and `data` go
to `send`, and `opened` to the rest, which also receives `sent`. The statement
`close_file(opened);` is a `let` whose variable is never used, and the last line
uses `sent`. Every variable appears in exactly one leaf. That is the usage theorem
for one program, and the derivation is the certificate.

The bug in `upload_twice` is a contraction, and the crate finds no split:

```text
{{#include ../../code/rust/output/ch22_affine_checker.txt:51:59}}
```

The bug in `upload_leaky` is different: the file is never closed. The crate
*accepts* it, and only notes that `opened` was discarded without use:

```text
{{#include ../../code/rust/output/ch22_affine_checker.txt:43:50}}
```

This is affine typing working as designed. Weakening is allowed, so a value may be
abandoned, and the type system cannot force us to call `close_file`. In Rust
the `File` would be closed anyway, by its destructor, when `opened` goes out of
scope. Whether a type system *can* force a value to be consumed, and why Rust
chose not to, is the subject of Chapter 24.

The same program in Lean needs the environment in the context. The functions
are curried, since the calculus has one-argument functions:

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:upload}}
```

```lean
{{#include ../../code/lean/Book/Ch22/Checker.lean:upload_eval}}
```

The leftovers say the same as the crate: everything is consumed by `upload`,
and `uploadLeaky` leaves `close_file` unused. The last line turns the checker's
answer into a proof by completeness and soundness: `rfl` evaluates
`infer uploadCtx upload` and checks that it is a `some`, and `infer_iff`
converts that into a derivation. There is a difference with the crate, and it
is instructive. In Lean the three functions are ordinary variables of the
context, so they are resources too: a version of `upload_twice` would be
rejected already for calling `send` twice, before anyone looked at `data`. The
crate treats declared functions as constants that can be called again and
again, as Rust does. Why Rust may treat functions that way, while a closure that
captures a `String` can be called only once, is a question about which values
may be duplicated, and it is the subject of Chapter 23.

## Common confusions

**"Affine means every variable must be used."** It means the opposite bound:
*at most* once. A variable may be used zero times (weakening). Requiring at least
one use is relevant logic, and exactly one use is linear logic; Rust has neither
(Chapter 24).

**"The `case` rule uses the context twice, so it is contraction."** Contraction
duplicates a resource for two consumers that *both* run. The branches of a
`case` are alternatives, only one of which runs, so each resource is still
consumed at most once on every run. The same holds for the two components of an
offer. The usage theorem counts them with $\max$ for exactly this reason.

**"E0382 points at the second use, so the second use is the bug."** The derivation
fails at a split, and both uses take part in it: rustc labels both. Fixing the
program may mean changing the first use (borrowing instead of moving, or
cloning) as often as the second.

**"Partial moves contradict the rule that `⊗` has no projections."** They refine
it. The calculus counts uses of variables; rustc counts uses of places. A pair
whose two fields are moved separately is used once per field, which is the same
discipline at a finer grain.

**"A closure in the calculus borrows what it uses."** It takes it. In
$\lambda^{\mathsf{aff}}$ every use is a move, so a closure that mentions a
variable owns it. Rust closures that only read a variable capture a *reference*
to it instead, which is a borrow, and borrowing is not part of the affine
calculus (Part VI).

**"The algorithmic checker is a different type system."** It is the same one,
presented differently. Soundness and completeness say that it accepts exactly
the typable terms, and the leftovers are exactly the unused part of the context.

## Summary

- $\lambda^{\mathsf{aff}}$ has unit, affine functions $\tau \multimap \sigma$,
  pairs $\tau \otimes \sigma$, offers $\tau \mathbin{\&} \sigma$ and sums
  $\tau \oplus \sigma$. Its typing rules split the context when both subterms
  run and share it when only one of two alternatives runs.
- Weakening is built into A-Var and A-Unit, and it is admissible for all
  derivations. Contraction is not: $\lambda x.\,(x, x)$ has no type, and rustc's
  E0382 is the report of the failed split.
- A pair is taken apart with `let`, which binds both components with one use of
  the pair. Projections can be defined but not both used; Rust refines the
  discipline to places, which explains partial moves.
- The usage theorem: in a well-typed term every variable is used at most once,
  counting alternatives with $\max$. Its Lean proof rests on one lemma: a split
  hands out exactly what the context had.
- Substitution and preservation hold; in a sharing rule a value is copied into
  both alternatives, but only one copy can run.
- The algorithmic checker threads input and output contexts ("leftovers"),
  forking and meeting them at offers and branches. Lean proves it sound and
  complete, so it decides typability.
- The `affine` crate implements the algorithm for a Rust-like syntax, tracks moves
  per place, prints derivations, and reproduces the core of rustc's E0382
  messages.

## Exercises

1. Show that $\tau \multimap \sigma \multimap \tau$ is inhabited in
   $\lambda^{\mathsf{aff}}$ but would not be in a linear calculus with rule L-Var.
   Then show that the term $\lambda f.\,\lambda a.\,f\,a\,a$ has no type of the form
   $(\tau \multimap \tau \multimap \sigma) \multimap \tau \multimap \sigma$ in
   $\lambda^{\mathsf{aff}}$. Which structural rule does each term need?
   *Hint:* the first is the K combinator and needs weakening; the second is W.
   For W, follow the splits until $a$ has to go to two places.

2. Find closed terms of types $(\tau \otimes \tau) \multimap \tau$ and
   $(\tau \mathbin{\&} \tau) \multimap \tau$. Which of the two would still be
   inhabited in the linear calculus?
   *Hint:* one of them throws a component away, the other chooses an alternative
   and throws nothing away.

3. In Lean, define the *linear* variant of the typing relation: copy `HasType`
   to a new `LHasType` in which `var` requires every other position to be a hole
   and `unit` requires the whole context to be holes. Prove that
   `discard Str File` has no linear type.
   *Hint:* define `allHoles : Ctx → Prop` (for example
   `∀ o ∈ Γ, o = none`). After two `cases` on the `lam` constructors, the `var`
   premise must hold for the context `[some File, some Str]`, and `simp` refutes it.

4. In Lean, prove that the checker never creates resources: if
   `infer Γ e = some (τ, Δ)` then `Wk Δ Γ`.
   *Hint:* `infer_sound` gives a split of `Γ` into `U` and `Δ`. Prove a lemma
   `Split.wk_right : Split Γ Γ₁ Γ₂ → Wk Γ₂ Γ`, by induction on the split, in the
   style of `Split.wk_left`.

5. Add an `if` expression to the `affine` crate, with a condition of type `bool`
   and two branches that share the context like the arms of a `match`. Write tests
   showing that a variable may be moved in both branches, and that a variable
   moved in one branch is moved after the `if`.
   *Hint:* parse `if e { e1 } else { e2 }` in `primary`, and copy the structure of
   `infer_match`, including the call to `merge`.

6. Suppose we add general recursion, a term $\mathsf{fix}\,f.\,e$ with the rule
   "if $\Gamma, f : \tau \multimap \sigma \vdash e : \tau \multimap \sigma$ then
   $\Gamma \vdash \mathsf{fix}\,f.\,e : \tau \multimap \sigma$". Does the usage
   theorem survive? What do we lose?
   *Hint:* look at the proof's case for A-Abs; it has the same shape. What is
   lost is termination, and with it the reading of types as theorems
   (Chapter 10): $\mathsf{fix}\,f.\,f$ inhabits every function type.
