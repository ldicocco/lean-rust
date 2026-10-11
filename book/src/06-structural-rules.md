# The Structural Rules

Every rule of natural deduction in Chapter 4 was about a connective. Rule ∧I
says how to prove a conjunction, rule →E says how to use an implication, and
so on down the list. There is a second kind of rule, which mentions no
connective at all. It talks only about the *context*, the list of assumptions
to the left of the turnstile. It says that you may reorder the assumptions,
that you may add an assumption you will never use, and that two copies of the
same assumption may be merged into one. These are the **structural rules**:
exchange, weakening and contraction. In ordinary logic they are so harmless
that most textbooks never state them, and Chapter 4 did not state them either.

This chapter is short on new machinery, but it contains the idea that the
second half of the book is built on. Whether a logic has these rules decides
what an assumption *is*. With all three, an assumption is a fact: once you
know it, you know it as many times as you like, and you are free to ignore
it. Without contraction, an assumption is a resource, like a coin that can be
spent once. Every time the Rust compiler reports error E0382, "use of moved
value", it is refusing to apply contraction.

**In this chapter you will learn:**

- what exchange, weakening and contraction say, and how to read them in both
  directions;
- the difference between primitive, derivable and admissible rules, and between
  contexts as lists, multisets and sets;
- why the natural deduction of Chapter 4 has all three structural rules without
  stating them, with a Lean proof by induction on derivations;
- how to count how many times a derivation uses an assumption, and how each
  structural rule changes the count;
- where the three rules show up in Rust: unused values and `drop`, moves and
  E0382, `Clone` and `Copy`, evaluation order and drop order;
- the resource reading of assumptions, and the design decision that generates
  the substructural logics of Part V.

## Rules about contexts

### The context, once more

Chapter 4 wrote natural deduction in sequent notation. A sequent
$\Gamma \vdash A$ says "from the assumptions in $\Gamma$, the formula $A$
follows", and the context $\Gamma$ is a list of formulas. Here are four of the
rules again, to have them in front of us:

$$
\dfrac{A \in \Gamma}{\Gamma \vdash A}\;\textsf{Hyp}
\qquad\qquad
\dfrac{\Gamma \vdash A \qquad \Gamma \vdash B}{\Gamma \vdash A \land B}\;{\land}\textsf{I}
$$

$$
\dfrac{\Gamma, A \vdash B}{\Gamma \vdash A \to B}\;{\to}\textsf{I}
\qquad\qquad
\dfrac{\Gamma \vdash A \to B \qquad \Gamma \vdash A}{\Gamma \vdash B}\;{\to}\textsf{E}
$$

Rule Hyp says that an assumption can be used. Rule →I is the one that changes
the context: to prove $A \to B$, add $A$ to the assumptions and prove $B$. The
comma in $\Gamma, A$ means "the list $\Gamma$ with $A$ added at the end". The
other rules pass the context along unchanged, from the conclusion to every
premise.

### The three structural rules

The structural rules are rules of the same shape, but no connective appears in
them. The only thing that changes between premise and conclusion is the
context:

$$
\dfrac{\Gamma_1, A, B, \Gamma_2 \vdash C}{\Gamma_1, B, A, \Gamma_2 \vdash C}\;\textsf{Exch}
$$

$$
\dfrac{\Gamma \vdash C}{\Gamma, A \vdash C}\;\textsf{Weak}
\qquad\qquad
\dfrac{\Gamma, A, A \vdash C}{\Gamma, A \vdash C}\;\textsf{Contr}
$$

**Exchange** (Exch) says that two neighboring assumptions may swap places.
Applied repeatedly, it puts the context in any order you like. **Weakening**
(Weak, also called *thinning*) says that if $C$ follows from $\Gamma$, it also
follows from $\Gamma$ with one more assumption. **Contraction** (Contr) says that
if $C$ follows from two copies of $A$, it also follows from one copy.

Gerhard Gentzen, who introduced both natural deduction and the sequent
calculus in 1935, stated these rules explicitly as rules of his sequent
calculus, and called them *structural* to set them apart from the *logical*
rules that introduce and eliminate connectives.

Like every rule, these can be read in two directions, and both readings are
useful.

| Rule | Top-down (building a proof) | Bottom-up (searching for one) | An assumption... |
|---|---|---|---|
| Exch | swap two assumptions | swap two assumptions | can be used in any position |
| Weak | add an assumption | throw an assumption away | may go unused |
| Contr | merge two copies into one | duplicate an assumption | may be used more than once |

> [!WARNING]
> The rules are stated in the direction that is convenient for proofs by
> induction, and that direction is the *opposite* of the slogans. Weakening, read
> top-down, makes the context *bigger*; the slogan "you may throw an assumption
> away" is the bottom-up reading: to prove $\Gamma, A \vdash C$ it is enough to
> prove $\Gamma \vdash C$, so $A$ was discarded. Contraction, read top-down,
> *merges* two copies; the slogan "you may duplicate an assumption" is again the
> bottom-up reading. When Part V says "affine means no contraction, so a value is
> used at most once", it is the bottom-up reading that is meant.

### The same rules with terms

Chapter 1 introduced typing judgments $\Gamma \vdash e : \tau$, where the context
gives types to variables. The structural rules have a version for them, and it is
the version that will matter most for Rust:

$$
\dfrac{\Gamma_1, x : \sigma, y : \tau, \Gamma_2 \vdash e : \rho}{\Gamma_1, y : \tau, x : \sigma, \Gamma_2 \vdash e : \rho}\;\textsf{Exch}
$$

$$
\dfrac{\Gamma \vdash e : \rho}{\Gamma, x : \sigma \vdash e : \rho}\;\textsf{Weak}
\qquad\qquad
\dfrac{\Gamma, x : \sigma, y : \sigma \vdash e : \rho}{\Gamma, z : \sigma \vdash e[z/x, z/y] : \rho}\;\textsf{Contr}
$$

Read each rule as a statement about the program $e$:

- **Exchange** leaves the program unchanged. Reordering the variables in scope
  does not change what the program means.
- **Weakening** also leaves the program unchanged, while the context grows. So the
  new variable $x$ does *not occur* in $e$: weakening is the permission to have a
  variable in scope and not use it.
- **Contraction** changes the program: $e[z/x, z/y]$ is $e$ with both $x$ and $y$
  replaced by $z$ (Chapter 7 defines substitution carefully). Where $e$ used two
  different variables, the new program uses the same variable $z$ twice:
  contraction is the permission to use a variable more than once.

This gives the sentence that the rest of the book turns on:

$$
\textbf{weakening} = \text{discarding} \qquad\qquad \textbf{contraction} = \text{duplicating}
$$

You can already see where Rust stands. A function `fn first<A, B>(a: A, b: B) -> A { a }`
never uses `b`; that is weakening, and Rust accepts it. A function
`fn dup<T>(x: T) -> (T, T) { (x, x) }` uses `x` twice; that is contraction, and
Rust rejects it unless `T` is `Copy`. We will look at both in detail below.

## Where the structural rules hide

Look back at the rules of Chapter 4: there is no exchange, no weakening and no
contraction among them. And yet natural deduction can prove $A, B \vdash A$,
which seems to need weakening (the $B$ is never used), and $A \vdash A \land A$,
which seems to need contraction (the $A$ is used twice). The structural rules are
there; they are just hidden in two places.

**The hypothesis rule.** Rule Hyp asks only that $A \in \Gamma$. It does not care
*where* in $\Gamma$ the formula sits (that is exchange), it does not care what
else is in $\Gamma$ (that is weakening), and it does not care how many times $A$
occurs in $\Gamma$ (that is contraction, read the other way). The leaves of every
derivation quietly absorb all three rules.

**Context sharing.** Rules with several premises, such as ∧I, →E and ∨E, hand the
*same* context $\Gamma$ to every premise. Each premise is free to use any
assumption in $\Gamma$, so a single assumption can be used once in each branch.
That is contraction, built into the shape of the rules.

Here is the clearest example, the commutativity of conjunction. (We write the
leaves as Hyp steps with their membership premise left implicit.)

$$
\dfrac{\dfrac{\dfrac{}{A \land B \vdash A \land B}\;\textsf{Hyp}}{A \land B \vdash B}\;{\land}\textsf{E}_2 \qquad \dfrac{\dfrac{}{A \land B \vdash A \land B}\;\textsf{Hyp}}{A \land B \vdash A}\;{\land}\textsf{E}_1}{A \land B \vdash B \land A}\;{\land}\textsf{I}
$$

There is one assumption, $A \land B$, and it is used twice, once by each
projection. Rule ∧I sent the context to both premises, and both premises used it.
This is a surprise the first time you see it: swapping the components of a pair
"needs" contraction in natural deduction. In Rust, `fn swap<A, B>((a, b): (A, B)) -> (B, A)`
does not need `Clone`: the pattern `(a, b)` takes the pair apart *once*, producing
two new variables that are used once each. Chapter 21 explains that Rust's pair
behaves like a different conjunction, written $\otimes$, whose elimination rule is
exactly this pattern match.

The second example shows weakening at a leaf. To prove $\vdash A \to (B \to A)$,
apply →I twice and then Hyp:

$$
\dfrac{\dfrac{\dfrac{A \in A, B}{A, B \vdash A}\;\textsf{Hyp}}{A \vdash B \to A}\;{\to}\textsf{I}}{\vdash A \to (B \to A)}\;{\to}\textsf{I}
$$

The assumption $B$ was added by →I and never used: rule Hyp simply ignored it.

### The same examples in Lean

The Lean code for this chapter is in `code/lean/Book/Ch06/Structural.lean` and
`code/lean/Book/Ch06/Usage.lean`. The first file starts by redefining the formulas
and the derivability relation of Chapter 4 (each chapter's Lean files are
self-contained, so we do not import Chapter 4's):

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:formula}}
```

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:proves}}
```

One detail needs attention. Lean lists are built from the front: `A :: Γ` is the
list `Γ` with `A` added *before* its first element. So where the mathematics
writes $\Gamma, A$, the Lean rules write `A :: Γ`, and the list `[A, B]` is the
context with `A` first. The order is different, and as you will see in a moment,
it makes no difference at all: that is precisely what exchange says.

The examples above, checked by Lean:

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:examples}}
```

`List.mem_cons_self` is the library fact that the head of a list is a member of
it ($a \in a :: l$). Where Lean can figure out which formula is meant, we let
`by simp` prove the membership instead. Notice that each proof is a tree of
constructors with the same shape as the derivation on paper: `.conjI` has two
children, each `.conjE₂` or `.conjE₁` has one, and the leaves are `.hyp`.

## Primitive, derivable and admissible

We keep saying that natural deduction "has" the structural rules without listing
them. To make that precise we need to distinguish three ways in which a rule can
belong to a system.

- A rule is **primitive** if it is one of the rules that define the system. The
  constructors of `Proves` are the primitive rules of our natural deduction.
- A rule is **derivable** if there is a fixed scheme that builds a derivation of
  its conclusion from derivations of its premises, using primitive rules only. A
  derivable rule is an abbreviation, a macro: wherever you use it, you could
  paste in the same few primitive steps instead.
- A rule is **admissible** if, whenever its premises are derivable, its
  conclusion is derivable too. The derivation of the conclusion may depend on the
  *shape* of the derivations of the premises; typically it is built by induction
  on them.

Every derivable rule is admissible: if the premises have derivations, plug them
into the macro. The converse fails, and the structural rules are the standard
examples. In natural deduction with lists as contexts, exchange, weakening and
contraction are admissible but not derivable: there is no fixed combination of
primitive rules that turns a derivation of $\Gamma \vdash C$ into one of
$\Gamma, A \vdash C$ without looking inside it, because no primitive rule adds an
unused assumption to a context. What we can do is walk through the whole
derivation and add $A$ to every context in it.

A programmer's way to see the difference: a derivable rule is a function that
wraps its argument in a few constructors and never inspects it; an admissible
rule is a recursive function that takes its argument apart and rebuilds it, like a
compiler pass over a syntax tree.

The difference matters when a system changes. If you add new primitive rules to a
system, every derivable rule stays derivable: the macro still works. An admissible
rule may stop being admissible, because its proof by induction now has a new case
to handle, and that case may fail. Exercise 5 adds a single axiom to natural
deduction and breaks weakening. Part V is full of systems designed so that
weakening or contraction is *not* admissible, and the main danger there is a
connective rule that brings a structural rule back without anyone noticing.

### Lists, multisets and sets

There is a third status, which is not about rules at all but about data
structures. If contexts are *sets* rather than lists, then $\Gamma, A, B$ and
$\Gamma, B, A$ are the same set, and so are $\Gamma, A, A$ and $\Gamma, A$.
Exchange and contraction are then **built in**: they do not say anything, because
the two contexts they relate are equal. The choice of data structure decides
which structural rules come for free:

| Contexts are | Exchange | Contraction | Weakening |
|---|---|---|---|
| lists | a statement | a statement | a statement |
| multisets | built in | a statement | a statement |
| sets | built in | built in | a statement |

A **multiset** is a collection in which order does not matter but multiplicity
does: $\{A, A, B\}$ and $\{A, B, A\}$ are the same multiset, while $\{A, A, B\}$
and $\{A, B\}$ are different. Weakening is a statement in all three cases, since
adding an element does change a list, a multiset and a set.

![Contexts as lists, multisets and sets. Exchange forgets the order of assumptions, contraction forgets their multiplicity; each choice of data structure suits a different family of logics.](../images/ch06-contexts.svg)

Mathlib has all three data structures, and it is instructive to see Lean confirm
the table:

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:lists_multisets_sets}}
```

`Multiset Formula` is Mathlib's type of multisets, and `A ::ₘ Γ` adds one copy of
`A` to the multiset `Γ`. `Multiset.cons_swap` is exactly exchange as an
*equation*. `Finset Formula` is the type of finite sets, `insert A Γ` adds `A`,
and `Finset.insert_idem` (idempotence: inserting twice is inserting once) is
contraction as an equation. The two inequalities are checked by `decide`, which
computes both sides and compares them.

Most presentations of ordinary logic use sets of assumptions and never mention
the structural rules. That is a reasonable choice when the rules are all
harmless. Substructural logic begins by refusing it: ordered logic keeps
contexts as lists, linear and affine logic use multisets, and the question "is
contraction admissible?" becomes the central design question.

## Admissibility, proved in Lean

Our Lean contexts are lists, so all three structural rules are statements that
need proofs. Let us prove them.

### A first attempt, and why it fails

The natural first try is to prove weakening directly: if `Proves Γ C`, then
`Proves (A :: Γ) C`, by induction on the derivation of `Γ ⊢ C`. Most cases are
easy. In the case of rule Hyp, we know `C ∈ Γ`, so `C ∈ A :: Γ`. In the case of
∧I, the induction hypotheses give derivations of `A :: Γ ⊢ C₁` and
`A :: Γ ⊢ C₂`, and ∧I combines them.

The case of →I breaks. There, `C` is `B → D` and the premise is
`B :: Γ ⊢ D`. The induction hypothesis, applied to the premise, adds `A` at the
front of *its* context and gives `A :: B :: Γ ⊢ D`. But to apply →I and obtain
`A :: Γ ⊢ B → D`, we need `B :: A :: Γ ⊢ D`, with `B` at the front, where →I
discharges it. The two contexts differ by an exchange. We are trying to prove
weakening and we need exchange; if we tried to prove exchange first, we would
run into the same problem one level down.

This is a very common situation in proofs by induction: the statement is true but
too weak to be its own induction hypothesis. The cure is to prove something
*stronger*, a statement general enough that the induction hypothesis is exactly
what each case needs.

### Monotonicity

The stronger statement is this: if every assumption of `Γ` is also an assumption
of `Δ`, then everything provable from `Γ` is provable from `Δ`. The relation
"every element of `Γ` is an element of `Δ`" is `Γ ⊆ Δ` (`List.Subset`), and the
theorem is called *monotonicity*, because derivability only grows as the context
grows.

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:mono}}
```

Let us go through it.

- `induction h generalizing Δ with` starts an induction on the derivation `h`, one
  case per rule, just like the soundness proof of Chapter 4. The words
  `generalizing Δ` matter. Without them, the induction hypothesis would be about
  the *fixed* `Δ` of the statement. With them, the induction hypothesis says
  "for every `Δ` with `Γ' ⊆ Δ`, ...", where `Γ'` is the context of the premise.
  We need that freedom, because in the →I and ∨E cases the premise's context is
  bigger than `Γ` and we must use the hypothesis with a bigger `Δ` too.
- In the `hyp` case, the derivation is a single leaf, `mem : C ∈ Γ`. The subset
  relation is, by definition, a function from membership in `Γ` to membership in
  `Δ`, so `sub mem : C ∈ Δ`, and `.hyp (sub mem)` is the new leaf. This is the
  *only* case where the context is looked at.
- In the cases that keep the context (`botE`, `conjI`, `conjE₁` and the rest), we
  apply the induction hypotheses with the same `sub` and rebuild the node with the
  same rule. This is where the transformation is a "compiler pass": it rebuilds
  the tree node by node.
- In the `impI` case, the premise lives in `A :: Γ`. We need a derivation in
  `A :: Δ`, and `List.cons_subset_cons` turns `sub : Γ ⊆ Δ` into
  `A :: Γ ⊆ A :: Δ`. The induction hypothesis, used with `A :: Δ`, gives what →I
  needs. The `disjE` case does the same for both branches.

The →I case that defeated the first attempt is now trivial: the induction
hypothesis does not care where in `Δ` the new formula goes, so no exchange is
needed.

### The three rules as corollaries

With monotonicity, the structural rules are one-liners, because each of them
relates two contexts with the same elements, or a context to a bigger one:

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:weakening}}
```

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:exchange}}
```

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:contraction}}
```

For weakening, `List.subset_cons_self A Γ` is the library fact `Γ ⊆ A :: Γ`. For
exchange and contraction, we prove the subset relation by hand. `intro X hX`
takes an arbitrary formula `X` with `hX : X ∈ Γ₁ ++ A :: B :: Γ₂`, and the goal is
`X ∈ Γ₁ ++ B :: A :: Γ₂`. The `simp only` step rewrites both memberships with two
library lemmas, `List.mem_append` ($x \in l_1 ++ l_2 \leftrightarrow x \in l_1 \lor x \in l_2$)
and `List.mem_cons` ($x \in a :: l \leftrightarrow x = a \lor x \in l$). After it,
the hypothesis says `X ∈ Γ₁ ∨ X = A ∨ X = B ∨ X ∈ Γ₂` and the goal says
`X ∈ Γ₁ ∨ X = B ∨ X = A ∨ X ∈ Γ₂`. That is a propositional tautology, and
`tauto`, a Mathlib tactic that proves goals by propositional reasoning (splitting
`∧`, `∨` and `↔` in hypotheses and goals), finishes the proof.

Exchange is stated for an arbitrary position in the context (between `Γ₁` and
`Γ₂`), which is what rule Exch says. Weakening and contraction are stated at the
front, which is enough, since exchange can move any formula there.

In fact the same argument proves more: two contexts with the same elements prove
exactly the same formulas.

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:same_elements}}
```

The proof builds the two directions of the `↔` with the anonymous constructor
`⟨_, _⟩`, each direction a function that applies `mono`. For this system, a
context might as well be a set. That is the precise sense in which natural
deduction "has" all three structural rules.

### Derivable versus admissible, in Lean

The distinction between derivable and admissible rules is visible in the Lean
proofs. Here is a derivable rule:

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:derivable}}
```

The proof of `conj_comm_rule` is a fixed term built from primitive rules, with
`h` plugged in twice. It never inspects `h`. (It also uses `h` twice, which is
contraction by sharing once more.)

And here is a rule whose proof needs an admissible rule:

```lean
{{#include ../../code/lean/Book/Ch06/Structural.lean:admissible_use}}
```

To prove $(A \to \bot) \to \bot$ from $\Gamma$, we assume $A \to \bot$ and apply
it to $A$. But the derivation `h` proves $A$ from $\Gamma$, and we need $A$ in the
bigger context `imp A bot :: Γ`. No primitive rule does that, so we call
`weakening h`, which runs the whole induction of `Proves.mono` over `h`. The rule
`dni_rule` is admissible; whether it is also derivable is a different question,
and it is not answered by this proof.

## Counting uses

"The assumption is used twice", "the assumption is never used": these are
statements about derivations, and so far we have checked them by looking at
pictures. Let us make Lean count.

There is an obstacle. `Proves Γ C` is a proposition: it lives in `Prop`, and Lean
does not let you compute data, such as a number, from a proof of a proposition.
Lean treats any two proofs of the same proposition as interchangeable, so a
function that returned different numbers for different proofs would make no
sense. Chapter 10 explains this *proof irrelevance* in detail. For us it means
that to count we need derivations that are *data*: a type in `Type`, whose values
are trees we can inspect, just like the abstract syntax trees of Chapter 3.

### Positions

When we count uses, we must know *which* assumption a leaf uses. The leaf
`hyp mem` of `Proves` only records that the formula is a member of the context,
and if the context is `[A, A]`, that does not say which copy is meant. So the data
version refers to assumptions by position:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:var}}
```

`Var Γ A` is an **inductive family**: a type that depends on a context and a
formula. A value `x : Var Γ A` is evidence that `A` sits in `Γ`, and it also says
where. The constructor `here` points at the first element of a context `A :: Γ`
and has type `Var (A :: Γ) A`. The constructor `there` takes a position in `Γ` and
makes it a position in `B :: Γ`, one step further. So in the context `[A, B, C]`,
the value `there here` has type `Var [A, B, C] B` and points at `B`. `Var.idx`
turns a position into a number. (Programmers who have met de Bruijn indices will
recognize them here; Chapter 7 introduces them for the λ-calculus, and Chapter 8
uses the same idea for the variables of typed terms.)

### Derivations as data

The data version of natural deduction has the same rules as `Proves`, with
`Type` instead of `Prop` and a position in the hypothesis rule:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:deriv}}
```

The two versions agree. Forgetting the tree turns a `Deriv` into a `Proves`:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:to_proves}}
```

These two theorems are proved by recursion, written with pattern matching like a
function: each constructor of `Var` or `Deriv` is sent to the corresponding
proof, with recursive calls on the subtrees. (A proof by recursion on a tree and
a proof by induction on it are the same thing; the `induction` tactic writes the
recursion for you.)
The file also proves the converse, in the theorem
`proves_iff_nonempty : Proves Γ C ↔ Nonempty (Deriv Γ C)`, by an induction just
like the ones above. `Nonempty` is the proposition "this type has at least one
value", so the theorem says that `Proves Γ C` holds exactly when some tree of type
`Deriv Γ C` exists.

### The structural rules as renamings

In the data version, the structural rules become *renamings*: functions that send
each position of one context to a position of another context holding the same
formula. Renaming a derivation replaces every leaf `hyp x` by `hyp (ρ x)`:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:renaming}}
```

`Renaming Γ Δ` is the type of functions that, for every formula `A`, map positions
of `A` in `Γ` to positions of `A` in `Δ` (`abbrev` defines it as an abbreviation
that Lean unfolds freely). The function `Renaming.lift` extends a renaming to
contexts with one more formula in front; `Deriv.rename` uses it when it goes
under →I or into the branches of ∨E, where the context grows. A renaming is the
data version of `Γ ⊆ Δ`, and `Deriv.rename` is the data version of
`Proves.mono`. The three structural rules are three particular renamings:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:structural_renamings}}
```

Weakening shifts every position by one, to make room for the new assumption at
the front. Exchange swaps positions 0 and 1. Contraction sends *both* positions
0 and 1 to position 0, and shifts the others down. Each definition is by pattern
matching on the position: `.here` is position 0, `.there .here` is position 1,
and `.there (.there x)` is everything else.

### Counting

To count the leaves that use some position, we select positions with a
boolean-valued function and walk the tree:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:uses}}
```

`Sel Γ` assigns `true` or `false` to every position of `Γ`. `Deriv.uses` adds 1
for every leaf whose position is selected. When it goes under a binder (the body
of →I, the branches of ∨E), the context has one more formula in front, so the
selection is lifted: the new position 0 is not selected, and the old positions
keep their selection, one step further. `count d i` selects exactly position `i`,
and `usage d` lists the counts of all positions in order. Here are the
derivations from the beginning of the chapter, as data:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:usage_examples}}
```

The pictures were right. The swap uses its only assumption twice, `A, B ⊢ A`
uses `A` once and `B` never, modus ponens uses each of its two assumptions once,
and `A ⊢ A ∧ A` uses `A` twice.

These counts let us name the disciplines of Part V. Call a derivation *affine*
if every assumption is used at most once, *relevant* if every assumption is used
at least once, and *linear* if every assumption is used exactly once:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:disciplines}}
```

`Deriv.discipline` reports the most specific of the three (a linear derivation is
also affine and relevant). Only modus ponens is linear. The swap and the
duplication are relevant but not affine; `A, B ⊢ A` is affine but not relevant.

### How the structural rules change the counts

Now apply the structural rules to a derivation and watch the counts.
`twoCopiesD` proves `A, A ⊢ A ∧ A` using each copy once:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:usage_structural}}
```

Contraction merges the two copies, and the merged assumption is used twice.
Weakening adds a new assumption at the front, used zero times. Exchange swaps
the counts (here both are 1). These are not coincidences of the examples; they
are theorems. The cleanest statement is about contraction:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:count_contract}}
```

The uses of the merged assumption are the sum of the uses of the two copies. To
prove it we need a lemma about renaming in general:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:uses_rename}}
```

It says: to count the selected leaves of a renamed derivation, count the leaves
of the original derivation whose position is *sent* to a selected position. The
proof is an induction on the derivation, again generalizing over the target
context. In the `hyp` case both sides are the same expression, so `rfl` closes it.
In the cases with one subtree and no new assumption, the induction hypothesis is
exactly the goal (`exact ih ρ s`). In the cases with two subtrees,
`simp only [rename, uses, ihd, ihe]` unfolds one step of `rename` and of `uses`
and rewrites with the induction hypotheses. In the binder cases (`disjE` and
`impI`) we also need the fact that lifting a selection and lifting a renaming fit
together, which is the first of four small lemmas:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:lift_lemmas}}
```

Each of them is an equation between two selections, which are functions, so the
proof starts with `funext _ x`: two functions are equal if they agree on every
argument, here every formula `_` and position `x`. Then `cases x` splits into the
two kinds of position, `here` and `there x`, and the combinator `<;>` runs `rfl`
on both resulting goals. In each case both sides compute to the same boolean.

Two more lemmas, `Deriv.uses_none` (selecting nothing counts nothing) and
`Deriv.uses_or` (the count of a union plus the count of an intersection is the
sum of the counts), are proved by the same kind of induction; their proofs use
`omega`, the decision procedure for linear arithmetic, to add up the counts of
the subtrees.

Now read the proof of `count_contract` again. `unfold` replaces `contract` and
`count` by their definitions, and `rw [Deriv.uses_rename]` turns the left side
into a count over the original derivation `d`, with the selection "positions
that `mergeFirstTwo` sends to 0". The rewrite `← Deriv.uses_or` turns the right
side into a count of a union plus a count of an intersection. The two `have`
steps then prove that the selections are what we want. `hor` says that a position
is sent to 0 exactly when it is 0 or 1; it is proved by `funext` (two functions
are equal if they agree on every argument) and a case analysis with `rcases` on
the position (`here`, `there here`, or `there (there x)`), each case closed by
`simp` computing `Var.idx` and the boolean equalities. `hand` says that no
position is both 0 and 1. The final `rw` replaces the selections, counts nothing
for the empty intersection, and drops the `+ 0`.

The weakening and exchange theorems are proved the same way:

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:count_weaken}}
```

```lean
{{#include ../../code/lean/Book/Ch06/Usage.lean:count_exchange}}
```

Put together, these theorems say something worth stating in words. Exchange
moves counts around without changing them. Weakening introduces an assumption
with count 0, and leaves the other counts alone. Contraction is the only one of
the three that can produce a count greater than 1 from counts that were at most
1. So a logic without contraction keeps every assumption at *most once*, and a
logic without weakening keeps every assumption at *least once*. That is the
whole idea of Part V in one paragraph, and Chapter 22 proves the "at most once"
half as a theorem about a programming language.

## A first glance at Rust

The structural rules are about contexts, and in a program the context is the set
of variables in scope. So the question "which structural rules does Rust have?"
becomes "what may a Rust program do with the variables in scope?". The answers
are in this chapter's Rust example, `code/rust/examples/ch06_structural.rs`, and
in two programs that the compiler rejects.

One caveat first, the same one Chapter 1 made about typing rules. Rust has no
official formal semantics, and the part of the compiler that rejects a use of a
moved value is not literally a sequent calculus: it is a dataflow analysis over
the compiler's intermediate representation, which Chapter 29 describes. When we
say "Rust refuses contraction", we are describing the compiler's behavior with
the vocabulary of the rules. The description is accurate for the cases in this
chapter, and Parts V and VI refine it.

The example uses two kinds of values. A `Connection` is a resource: it is not
`Copy`, not `Clone`, and it prints a message when it is dropped. A `Coupon` can be
cloned, but it is not `Copy`.

```rust
{{#include ../../code/rust/examples/ch06_structural.rs:resources}}
```

### Exchange

Rust keeps exchange. The order in which variables were declared, or in which
parameters are listed, does not restrict how they can be used:

```rust
{{#include ../../code/rust/examples/ch06_structural.rs:exchange}}
```

But exchange is a statement about *typing*. Evaluation has an order, and Rust
fixes it: the operands of a tuple or the arguments of a call are evaluated left
to right, and local variables are dropped in the reverse order of their
declaration.

```rust
{{#include ../../code/rust/examples/ch06_structural.rs:exchange_demo}}
```

```text
{{#include ../../code/rust/output/ch06_structural.txt:1:9}}
```

The connection to the cache was opened second and is closed first. If you swap
the two `let` lines, the program still type checks, as exchange promises, but
the output changes. A logic does not see effects; a programming language must
specify them. Chapter 24 studies drop order in detail.

### Weakening, with an effect

Rust keeps weakening. A function may ignore a parameter:

```rust
{{#include ../../code/rust/examples/ch06_structural.rs:weakening}}
```

The leading underscore in `_unused` tells the compiler that the omission is
deliberate. Without it you would get a warning from the `unused_variables` lint,
and a warning is all you would get: a lint is advice, not a typing rule. A
language that rejected unused variables would be a *relevant* type system, and
Rust is not one.

What Rust adds to weakening is an effect. A value that goes unused is still
owned by someone, and when its owner goes out of scope, the value is dropped,
which runs its destructor:

```rust
{{#include ../../code/rust/examples/ch06_structural.rs:weakening_demo}}
```

```text
{{#include ../../code/rust/output/ch06_structural.txt:10:16}}
```

The audit connection is closed when `weaken` returns, before its result is
printed: the unused parameter was dropped at the end of the function's body. The
call `drop(unused)` is weakening made explicit. The standard library's
`std::mem::drop` is a function that takes its argument by value and does nothing
with it; its body is empty. Taking ownership and doing nothing is precisely
discarding an assumption, and the destructor runs because the argument goes out
of scope at the end of `drop`. Chapter 24 calls this *weakening with a side
effect* and studies its consequences.

### Contraction, refused

Rust does not have contraction for values that are not `Copy`. Here is a program
that uses a coupon twice:

```rust
{{#include ../../code/rust/compile_fail/ch06_use_after_move.rs:checkout}}
```

```text
{{#include ../../code/rust/compile_fail/ch06_use_after_move.stderr}}
```

Read the diagnostic with the rules in mind. "Move occurs because `coupon` has
type `Coupon`, which does not implement the `Copy` trait" says that the
assumption `coupon` is a resource, not a fact. "Value moved here" marks the first
use, which consumed it. "Value used here after move" marks the second use, which
would need contraction: the body uses one variable twice, which a typing
derivation could only justify by merging two assumptions `coupon1` and `coupon2`
into one. The compiler then offers two ways out. The first note suggests changing
`redeem` to *borrow* the coupon, so that using it does not consume it; borrowing
is the subject of Part VI. The second suggests implementing `Clone`, so that the
duplication is done explicitly by a function call.

### Contraction in a loop

A loop is a quieter way to ask for contraction. The body of a loop is checked
once but runs many times, so a value moved in the body would be used once per
iteration:

```rust
{{#include ../../code/rust/compile_fail/ch06_move_in_loop.rs:send_all}}
```

```text
{{#include ../../code/rust/compile_fail/ch06_move_in_loop.stderr}}
```

"Value moved here, in previous iteration of loop" is the compiler's way of saying
that the variable `conn` would be used as many times as there are orders. The fix
in the example program is to *borrow* the connection in the loop body, reading
`conn.host` through the variable without moving it out:

```rust
{{#include ../../code/rust/examples/ch06_structural.rs:loop_demo}}
```

```text
{{#include ../../code/rust/output/ch06_structural.txt:21:27}}
```

The connection is used three times and closed once, at the end of `main`.

### Contraction restored: `Clone` and `Copy`

There are two ways to get contraction back, and they are different in an
instructive way:

```rust
{{#include ../../code/rust/examples/ch06_structural.rs:contraction}}
```

`contract_clone` duplicates explicitly: the program calls `clone`, which may
allocate memory and run arbitrary code. In the vocabulary of this chapter,
`Clone` does not give you the structural rule; it gives you a *function* of type
`A -> (A, A)`, and the program calls it. `contract_copy` duplicates implicitly:
for `Copy` types, using a variable does not move it, the bits are copied, and
using `a` twice needs nothing at all. For the types that implement `Copy`
(integers, `bool`, `char`, shared references `&T`, and tuples and arrays of `Copy`
types), Rust *has* contraction, silently.

```rust
{{#include ../../code/rust/examples/ch06_structural.rs:contraction_demo}}
```

```text
{{#include ../../code/rust/output/ch06_structural.txt:17:20}}
```

The last line deserves a second look. A shared reference `&Coupon` is `Copy`, so
contraction applies to it: two references to the same coupon, as `std::ptr::eq`
confirms. Duplicating a reference does not duplicate the coupon; it duplicates a
*permission to read* it. That observation is the seed of Part VI, which argues
that references are better explained by permissions and regions than by
affinity.

Here is the summary of this first glance:

| Rule | In Rust | Observed as |
|---|---|---|
| Exchange | kept | order of `let`s and parameters is irrelevant to typing |
| Weakening | kept, with an effect | unused values are allowed; `Drop` runs at scope end |
| Contraction | refused for non-`Copy` values | E0382, "use of moved value" |
| Contraction | kept for `Copy` types | `i32`, `bool`, `&T` used any number of times |
| Contraction | explicit via `Clone` | a call to `clone()` |

Weakening without contraction has a name: it is the definition of an **affine**
discipline. This table is the first, rough evidence for the claim that Chapter 1
called the question of the book, and Chapter 33 returns to it with all the
evidence in hand.

## The resource reading of assumptions

Why would anyone want a logic without contraction? Because of what assumptions
stand for.

In mathematics, an assumption is a *fact*. If you know that $n$ is even, you can
use that fact once, twice or not at all, and it does not wear out. Contraction is
the right rule for facts, and so is weakening: an irrelevant fact does no harm.

Now let an assumption stand for a *thing*: a coin, a ticket, an open file, a
network connection, a heap buffer. Using it means spending it, handing it over,
closing it. Contraction is now the wrong rule: from one coin it would conclude
two. Jean-Yves Girard, who introduced *linear logic* in 1987, liked to explain it
with purchases. Suppose a coin buys a coffee. If assumptions may be duplicated,
then from one coin you get a coffee *and* still have the coin, and so you can
buy as many coffees as you like. A logic that talks about resources must not
have contraction.

Weakening is a subtler case. Throwing a thing away is sometimes fine (an unused
coupon can expire) and sometimes not (an opened transaction must be committed or
rolled back, a promise must be kept). A logic that keeps weakening but drops
contraction describes resources that may be discarded but not copied: it is
*affine*. A logic that drops both describes resources that must be used exactly
once: it is *linear*.

In a programming language, a variable of a type that owns something (a `String`
owns a heap buffer, a `File` owns a file descriptor) is exactly such an
assumption. Two uses of it would mean two owners of one buffer, and in a language
without a garbage collector, two owners means two frees: a double free, one of
the classic memory-safety bugs. Refusing contraction is how Rust rules it out
before the program runs.

### The design decision

The move that generates all of Part V is easy to state: take a logic and delete
some of its structural rules. What remains is a **substructural** logic. Which
rules you delete decides what an assumption is: facts (keep all three),
discardable resources (delete contraction), obligations that must be met (delete
weakening), resources that must be used exactly once (delete both), or even
resources that must be used in order (delete exchange as well).

But deleting a rule is not enough when the rule is hidden in other rules, and we
have seen that natural deduction hides contraction in rule ∧I. If the context
$\Gamma = x : A$ is given to *both* premises, both can use $x$, and contraction
is back no matter what we deleted. A substructural logic must replace context
*sharing* by context *splitting*: the conclusion's assumptions are divided
between the premises, each assumption going to exactly one of them. The
conjunction with a splitting rule is written $\otimes$ ("tensor"):

$$
\dfrac{\Gamma \vdash A \qquad \Delta \vdash B}{\Gamma, \Delta \vdash A \otimes B}\;{\otimes}\textsf{I}
$$

To prove $A \otimes B$ from $\Gamma, \Delta$, prove $A$ from $\Gamma$ and $B$ from
$\Delta$. Similarly, weakening hides in rule Hyp, which accepts any context that
contains $A$; a logic without weakening uses the stricter axiom $A \vdash A$, in
which the context is exactly $A$.

Splitting the context is literally what Rust does when it checks a call
`f(a, b)`: the owned variables in scope must be divided between the two
arguments, and if both arguments need the same non-`Copy` variable, no division
exists and the compiler reports E0382.

This is where the seed is planted. Part V grows it:

- Chapter 21 deletes the structural rules one by one and studies the resulting
  family of logics. It finds that, without contraction, conjunction splits into
  two different connectives ($A \otimes B$, which splits the context, and
  $A \mathbin{\&} B$, which shares it), and it builds a proof search for linear and
  affine logic that shows exactly which sequents survive.
- Chapter 22 builds an affine λ-calculus, with the typing rules of a small
  programming language, and proves that every variable is used at most once.
- Chapter 23 explains `Copy` and `Clone` as a controlled way to bring contraction
  back, the *exponential* modality of linear logic.
- Chapter 24 studies weakening with a side effect: `Drop`, leaks and why Rust is
  affine rather than linear.
- Chapter 25 uses affinity to put protocols into types.

## Putting it together: one formula, three views

Let us follow a single formula through the whole chapter: $A \to A \land A$,
"from $A$, conclude $A$ and $A$". Its proof needs one assumption twice, so it is
the purest test of contraction.

**The mathematics.** In natural deduction, →I reduces the goal to
$A \vdash A \land A$, and ∧I splits it into two premises that both receive the
context $A$:

$$
\dfrac{\dfrac{\dfrac{A \in A}{A \vdash A}\;\textsf{Hyp} \qquad \dfrac{A \in A}{A \vdash A}\;\textsf{Hyp}}{A \vdash A \land A}\;{\land}\textsf{I}}{\vdash A \to A \land A}\;{\to}\textsf{I}
$$

With an explicit contraction step, the same proof reads: prove $A, A \vdash A \land A$
using each copy once, then contract. In a logic with ⊗I instead of ∧I and
without contraction, the context $A$ would have to be split between the two
premises, one of them would receive nothing, and the proof would fail. Chapter 21
proves, in Lean, that $A \vdash A \otimes A$ has *no* derivation at all in linear
logic, by an invariant that counts atoms.

**Lean.** The derivation `dupD` has usage `[2]`. The derivation `twoCopiesD` of
`A, A ⊢ A ∧ A` has usage `[1, 1]`: it is linear. Applying `Deriv.contract` to
it produces a derivation with usage `[2]`, and the theorem `count_contract`
guarantees that this is no accident: contraction adds the counts.

**Rust.** The formula becomes a generic function type, `fn dup<T>(x: T) -> (T, T)`.
With the body `(x, x)` and no bound on `T`, the compiler rejects it with E0382,
exactly as it rejected `checkout`. With the bound `T: Clone`, the body
`(x.clone(), x)` is accepted: contraction paid for by a function call. With the
bound `T: Copy`, the body `(x, x)` is accepted as it stands: contraction built
in for a class of types. Three bodies, three different relationships with one
structural rule.

Compare $A \to (B \to A)$, which needs weakening instead. Lean's `firstD` has
usage `[1, 0]`, an affine derivation. Rust's `weaken` compiles without
complaint and drops its second argument. One structural rule is kept, the other
is not: that asymmetry is the shape of Rust's ownership discipline.

## Common confusions

**"Weakening means deleting an assumption."** Read top-down, weakening *adds* an
assumption to the context of a sequent that was already provable. The intuition
"discard an assumption" is the bottom-up reading, from the goal toward the
premises. Both are correct readings of the same rule; mixing them up makes
statements like "affine logic has weakening" sound backwards.

**"Natural deduction has structural rules among its rules."** It does not, in the
presentation of Chapter 4. The structural rules are admissible: they are
theorems *about* the system, proved by induction, not rules *of* the system. Some
presentations (especially of the sequent calculus) include them as primitive
rules; the derivable sequents are the same either way.

**"Rust has no contraction."** Rust has no *implicit* contraction for values that
are not `Copy`. For `Copy` types, including every shared reference `&T`,
contraction is silent and free, and `Clone` provides explicit duplication for
many other types. Saying exactly where contraction is available is a large part
of the answer to the book's question.

**"The unused-variable warning means Rust requires every variable to be used."**
It is a lint, and it can be silenced with a leading underscore or turned off.
A type system that required every variable to be used would be relevant, and
`#[must_use]`, which Chapter 24 discusses, is the closest Rust comes to it.

**"Exchange means that evaluation order does not matter."** Exchange says that
the order of assumptions does not matter for *derivability*, or for typing. Rust
evaluates operands left to right and drops locals in reverse order of
declaration, and programs can observe both.

**"An admissible rule is weaker than a derivable one."** For the system as it is,
they license exactly the same conclusions. The difference is robustness: a
derivable rule survives the addition of new rules, while an admissible rule must
be proved again, and may fail.

## Summary

- The structural rules (exchange, weakening, contraction) mention no connective;
  they say what may be done with the context. Weakening is discarding, contraction
  is duplicating, exchange is freedom of order.
- Read top-down, weakening adds and contraction merges; the slogans "discard" and
  "duplicate" are the bottom-up readings.
- A rule can be primitive, derivable (a fixed macro of primitive rules) or
  admissible (its conclusion is derivable whenever its premises are, usually by
  induction). Derivable rules survive extensions of a system; admissible ones may
  not.
- Contexts can be lists, multisets or sets. Multisets build exchange in; sets also
  build in contraction.
- Natural deduction has all three structural rules, admissibly. They hide in the
  hypothesis rule and in the sharing of contexts between premises. Lean proves it
  through monotonicity: `Proves Γ C` and `Γ ⊆ Δ` give `Proves Δ C`.
- With derivations as data, the structural rules are renamings of positions.
  Weakening adds an assumption used zero times; contraction adds up the uses of
  two assumptions; only contraction can push a count above one.
- Rust keeps exchange (with a fixed evaluation and drop order), keeps weakening
  (with the effect of running destructors), refuses contraction for non-`Copy`
  values (E0382), restores it for `Copy` types, and offers it explicitly via
  `Clone`.
- An assumption can be a fact or a resource. Deleting structural rules, and
  replacing context sharing by context splitting, gives the substructural logics
  of Part V.

## Exercises

1. Write out, on paper, the case for rule ∨E in the proof that weakening is
   admissible: assume derivations of $\Gamma \vdash A \lor B$,
   $\Gamma, A \vdash C$ and $\Gamma, B \vdash C$, and build one of
   $\Gamma, D \vdash C$. Where do you need exchange, if you insist on adding $D$ at
   the end of the context?
   *Hint:* the induction hypothesis applied to the second premise gives
   $\Gamma, A, D \vdash C$, but ∨E needs a premise whose context ends with $A$.

2. In Lean, prove contraction at an arbitrary position:
   `theorem contraction_mid (h : Proves (Γ₁ ++ A :: A :: Γ₂) C) : Proves (Γ₁ ++ A :: Γ₂) C`.
   Then prove `Proves [A, B, A] C → Proves [B, A] C` using only `exchange`,
   `contraction` and `weakening` (not `Proves.mono`).
   *Hint:* for the first, imitate the proof of `exchange`. For the second, bring
   the two copies of `A` next to each other first: `exchange (Γ₁ := [A])` swaps the
   second and third formulas, and `exchange (Γ₁ := [])` swaps the first two. The
   whole proof is one line.

3. Build a `Deriv` of $A \to B, A \to C, A \vdash B \land C$ in Lean and
   `#eval` its usage. Is it affine, relevant, linear? Then build a derivation of
   $(A \to A \to B) \to A \to B$ (an open version is enough:
   $A \to A \to B, A \vdash B$) and check that it uses the assumption $A$ twice.
   *Hint:* the context is `[imp A B, imp A C, A]`, and `A` is at position
   `.there (.there .here)`. The second formula is the logician's combinator W,
   the standard test for contraction.

4. Write three Rust functions with the types of the formulas
   $A \land B \to A$, $(A \to B) \to (A \to C) \to A \to B \land C$ and
   $A \land B \to B \land A$, for generic `A`, `B`, `C` with no trait bounds (use
   `FnOnce` for the function arguments). Which ones compile? For the one that does
   not, say which structural rule it needs and add the smallest trait bound that
   makes it compile.
   *Hint:* in the second, the argument of type `A` is needed by both functions.

5. Add a new primitive rule to `Proves`: the axiom `Proves [] (atom "p")`, which
   is available only in the empty context. Show that weakening is no longer
   admissible: `Proves [] (atom "p")` holds but `Proves [atom "q"] (atom "p")` does
   not. Why does adding the same axiom in every context, `Proves Γ (atom "p")`,
   keep weakening admissible?
   *Hint:* in every rule, the contexts of the premises contain the context of
   the conclusion, so a derivation of $q \vdash p$ never reaches the empty
   context. Without the new axiom, a truth-table argument (Chapter 4's soundness
   theorem) shows that $q \vdash p$ is not derivable.

6. The theorem `count_weaken` is about weakening at the front of the context.
   State and prove in Lean that weakening does not change the *total* number of
   hypothesis leaves: `(d.weaken (B := B)).uses (fun _ _ => true) = d.uses (fun _ _ => true)`.
   *Hint:* rewrite with `Deriv.uses_rename`; the selection on the right-hand side
   is then the constant `true` function, and `rfl` may finish the proof.
