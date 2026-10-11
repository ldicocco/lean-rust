# A Core Calculus for Borrowing

Over the last six chapters we have collected the pieces of Rust's ownership
discipline one at a time: an affine λ-calculus (Chapter 22), `Copy` (Chapter
23), drops (Chapter 24), regions and the escape check (Chapter 26), subtyping
between lifetimes (Chapter 27). Each piece made sense on its own, and each came
with a promise that it explained some part of what the borrow checker does.

This chapter keeps those promises in the only way that is fully convincing: by
putting every piece into a single formal system and checking that it works. We
build a small calculus with owners, moves, drops, `Copy`, shared and mutable
borrows, lifetimes, reborrowing and the escape check, write down every typing
rule with the Rust program each premise models, and give it an operational
semantics in which reading freed memory or writing to a shared location are
*stuck* states, the formal counterpart of undefined behavior. Then we work through two derivations that every Rust
programmer has met in disguise: why a `&mut` reference can apparently be used
twice, and why the classic "push while iterating" bug has no derivation at all.

The calculus is in the spirit of the research calculi that formalize Rust's
core (Featherweight Rust and Oxide are two well-known ones), but much smaller:
small enough that a Rust crate can check its programs and print their
derivations, and that Lean can prove theorems about it in a few hundred lines.

**In this chapter you will learn:**

- how ownership, `Copy`, borrows and lifetimes fit into one type system,
  $\lambda^{\mathsf{aff}}_{\mathsf{rgn}}$, with thirteen typing rules;
- what every premise of the three borrow rules does, and which premises are
  affine bookkeeping and which are region reasoning;
- an operational semantics with a store and loan states, and what progress
  and preservation promise for it;
- why `bump(r); bump(r);` type-checks although `&mut` is not `Copy` (derivation
  I), and why the aliasing bug is rejected (derivation II);
- how the `borrowck` crate checks programs of the calculus, prints derivation
  trees, reports errors and runs programs on an abstract machine;
- how to state the rules in Lean, build a derivation as a proof term, prove that
  *no* derivation exists, and prove that a mutable reference is used at most
  once.

## What we need from Parts V and VI

Three ideas from earlier chapters carry this one. Here they are in the form we
will use them.

**Context splitting.** In the affine λ-calculus of Chapter 22, a rule with two
subterms does not give both of them the whole context. It *splits* the context:
$\Gamma = \Gamma_1 \uplus \Gamma_2$ means that every variable of $\Gamma$ goes
to $\Gamma_1$ or to $\Gamma_2$, so a variable can be used by one subterm or the
other, but not by both. That is how the type system forbids contraction, and it
is the formal version of a move: after `let t = s;` the variable `s` belongs to
the `let`'s right-hand side, so the rest of the block cannot use it (E0382).
Weakening is allowed: a variable may go unused, as in Rust, where an unused
value is simply dropped.

**`Copy` as permission to share a variable.** Chapter 23 refined the split: a
variable whose type satisfies the predicate $\mathsf{Copy}$ may go to *both*
halves. Contraction comes back, but only for the types where it is harmless.

**Regions and permissions.** Chapter 26 explained that affinity alone cannot
account for references: a shared reference is duplicable, so counting uses says
nothing about whether it outlives the data it points to. Lifetimes are *region
variables*: names for a stretch of the program during which a borrow is valid.
A reference type mentions its region (`&'a T`), and the **escape check** forbids
a value whose type mentions a region from leaving that region. A shared
reference is a duplicable read permission, a mutable reference a unique write
permission, and a borrow is a temporary transfer of permission from an owner.

Chapter 27's subtyping does not appear in this chapter. Our rules demand exact
equality of types where Rust would accept a reference with a longer lifetime
than needed, so the calculus rejects some programs that subtyping would rescue;
none of the programs we study needs it.

## The design of the calculus

Before the rules, four design decisions. Each one trades fidelity to Rust for a
system small enough to hold in your head.

**Owners are locations.** Borrowing needs something to point at. In our
calculus, a value that can be borrowed lives in a *store* (a heap), and its
owner is a pointer to that location, of type $\mathsf{Box}\,\tau$. Rust lets you
borrow any local variable (`&mut x`) as well as the contents of a `Box`; a
local variable lives in a stack frame, which is memory too, so modelling every
borrowable variable as an owned location loses nothing essential. A new
location is created with $\mathsf{new}\ e$, Rust's `Box::new(e)`.

**Borrows are lexically scoped.** A borrow is a construct with a body:
$\mathsf{borrow}\ y = \&^{\alpha} x\ \mathsf{in}\ e$ creates a reference $y$
that is valid exactly while $e$ runs. The lifetime $\alpha$ is introduced by the
construct, and its scope is the body. This is roughly how Rust worked before
non-lexical lifetimes arrived with the 2018 edition, when a borrow held in a
variable lasted until the end of that variable's scope; today's compiler
computes shorter lifetimes from the control-flow graph, and Chapter 29 is about
how.

**A borrow lends the owner and gives it back.** The borrow construct consumes
its owner, exactly as a function call consumes a moved argument, and returns it
when the body finishes, paired with the body's result. So the type of a borrow is
a pair $\mathsf{Box}\,\tau \otimes \sigma$: the owner, and whatever the body
computed. The program then rebinds the owner with a `let`:

$$
\mathsf{let}\ (x, n) = (\mathsf{borrow}\ y = \&^{\alpha} x\ \mathsf{in}\ {*y})\ \mathsf{in}\ \dots
$$

Rust hides this rebinding: after `let n = *(&x);` you still call the owner `x`.
Making it explicit is what lets plain affine context splitting express "you
cannot use the owner while it is borrowed": during the body, the owner belongs to
the borrow, not to anybody else.

**No functions.** The calculus has no λ, no function types and no lifetime
polymorphism. A Rust function `fn f<'a>(r: &'a mut i32) { body }` is modelled by
checking its body in a context where `'a` is a lifetime in scope and `r` has type
$\&^{\alpha}\mathsf{mut}\,\mathsf{Int}$, which is exactly what a function
signature means (Chapter 1 read signatures as judgments). A call is modelled by
inlining the callee. We keep the name $\lambda^{\mathsf{aff}}_{\mathsf{rgn}}$,
"affine, with regions", as a family name.

Here is the full list of what we leave out, so that you know what the calculus
does *not* claim to explain: functions and lifetime parameters on them, the
`'static` lifetime, outlives constraints (in a lexically scoped calculus they are
implicit: a lifetime introduced inside another one's scope is shorter),
subtyping and variance, structs and enums, partial moves out of places, moving a
value out of a box, reading through a `&mut`, `Drop` implementations, interior
mutability, and non-lexical lifetimes. Everything else, the things that make
borrowing borrowing, is in.

## Syntax

The types are integers, the unit type, pairs, owned locations and the two kinds
of reference. We write $\kappa$ for any lifetime and $\alpha$, $\beta$ for
lifetimes that a borrow introduces:

$$
\tau, \sigma \;::=\; \mathsf{Int} \mid \mathsf{Unit} \mid \tau_1 \otimes \tau_2 \mid \mathsf{Box}\,\tau \mid \&^{\kappa}\,\tau \mid \&^{\kappa}\mathsf{mut}\,\tau
$$

The pair type $\tau_1 \otimes \tau_2$ is the multiplicative conjunction of
Chapter 21, Rust's tuple `(T, U)`. $\&^{\kappa}\,\tau$ is Rust's `&'k T` and
$\&^{\kappa}\mathsf{mut}\,\tau$ is `&'k mut T`. The free lifetimes of a type,
$\mathrm{flv}(\tau)$, are the lifetimes it mentions:
$\mathrm{flv}(\&^{\kappa}\mathsf{mut}\,(\mathsf{Int} \otimes \&^{\beta}\mathsf{Int})) = \{\kappa, \beta\}$.

The terms are the affine core of Chapter 22 without functions, plus allocation,
dropping, reading, writing and three ways to borrow:

$$
e \;::=\; x \mid n \mid () \mid (e_1, e_2) \mid \mathsf{let}\ x = e_1\ \mathsf{in}\ e_2 \mid \mathsf{let}\ (x, y) = e_1\ \mathsf{in}\ e_2 \mid \mathsf{new}\ e \mid \mathsf{drop}\ e
$$

$$
\mid\ {*e} \mid {*e_1} := e_2 \mid \mathsf{borrow}\ y = \&^{\alpha} e_1\ \mathsf{in}\ e_2 \mid \mathsf{borrow}\ y = \&^{\alpha}\mathsf{mut}\ e_1\ \mathsf{in}\ e_2
$$

$$
\mid\ \mathsf{borrow}\ y = \&^{\alpha}\mathsf{mut}\,{*e_1}\ \mathsf{in}\ e_2
$$

Each form has a Rust counterpart, and the `borrowck` crate reads programs in a
concrete syntax that stays close to Rust's:

| Calculus | Crate syntax | Rust |
|---|---|---|
| $\mathsf{new}\ e$ | `new e` | `Box::new(e)` |
| $\mathsf{drop}\ e$ | `drop e` | `std::mem::drop(e)` |
| ${*e}$ | `*e` | `*e` (copying a `Copy` value out) |
| ${*e_1} := e_2$ | `*e1 := e2` | `*e1 = e2;` |
| $\mathsf{borrow}\ y = \&^{\alpha} e_1\ \mathsf{in}\ e_2$ | `borrow y = &'a e1 in e2` | `{ let y = &e1; e2 }` |
| $\mathsf{borrow}\ y = \&^{\alpha}\mathsf{mut}\ e_1\ \mathsf{in}\ e_2$ | `borrow y = &'a mut e1 in e2` | `{ let y = &mut e1; e2 }` |
| $\mathsf{borrow}\ y = \&^{\alpha}\mathsf{mut}\,{*e_1}\ \mathsf{in}\ e_2$ | `borrow y = &'a mut *e1 in e2` | `{ let y = &mut *e1; e2 }` |

The last form is a **reborrow**: it creates a new mutable reference from an
existing one, the `&mut *r` that you rarely write because the compiler inserts
it for you. In all three borrow forms the lifetime $\alpha$ and the variable $y$
are bound in the body $e_2$, the way a `let` binds its variable.

### The syntax in Rust and in Lean

The crate's types and terms are ordinary Rust enums
(`code/rust/crates/borrowck/src/syntax.rs`):

```rust
{{#include ../../code/rust/crates/borrowck/src/syntax.rs:ty}}
```

```rust
{{#include ../../code/rust/crates/borrowck/src/syntax.rs:term}}
```

The last two variants of `Term` never appear in a program you write. They are
the run-time forms of the operational semantics, which we meet later: pointer
values into the store, and the frame of a borrow in progress. Keeping them in
the same enum mirrors the mathematics, where run-time forms extend the grammar
of terms.

The Lean version (`code/lean/Book/Ch28/Syntax.lean`) is the same two inductive
types, with variables and lifetimes named by strings so that the derivations we
build later read like the ones on paper:

```lean
{{#include ../../code/lean/Book/Ch28/Syntax.lean:ty}}
```

```lean
{{#include ../../code/lean/Book/Ch28/Syntax.lean:term}}
```

(The constructor names `letIn` and `refMut` avoid Lean's keywords `let` and
`mut`.) The free lifetimes of a type are a recursive function:

```lean
{{#include ../../code/lean/Book/Ch28/Syntax.lean:lfts}}
```

## `Copy` and context splitting

The predicate $\mathsf{Copy}(\tau)$ says that values of type $\tau$ may be
duplicated by simply using them twice. It is the least predicate closed under
four rules:

$$
\dfrac{}{\mathsf{Copy}(\mathsf{Int})}\;\textsf{C-Int}
\qquad
\dfrac{}{\mathsf{Copy}(\mathsf{Unit})}\;\textsf{C-Unit}
\qquad
\dfrac{}{\mathsf{Copy}(\&^{\kappa}\,\tau)}\;\textsf{C-Ref}
\qquad
\dfrac{\mathsf{Copy}(\tau_1) \qquad \mathsf{Copy}(\tau_2)}{\mathsf{Copy}(\tau_1 \otimes \tau_2)}\;\textsf{C-Pair}
$$

"Least" means that nothing else is `Copy`. In particular there is no rule for
$\mathsf{Box}\,\tau$ (an owner of a location: duplicating it would give the
location two owners, and two frees) and none for $\&^{\kappa}\mathsf{mut}\,\tau$
(a unique write permission: duplicating it would give two writers). Rule C-Ref
says that *every* shared reference is `Copy`, whatever it points to: `&String`
is `Copy` although `String` is not, because copying the reference copies the
read permission, not the string. Rule C-Pair is Rust's requirement that a type
can derive `Copy` only if all its fields are `Copy`.

In Lean the predicate is an inductive family with one constructor per rule, and
"no rule concludes `Copy (.box τ)`" becomes a one-line proof:

```lean
{{#include ../../code/lean/Book/Ch28/Syntax.lean:copy}}
```

```lean
{{#include ../../code/lean/Book/Ch28/Syntax.lean:not_copy}}
```

`nomatch h` asks Lean to consider every constructor that could have produced
`h : Copy (.box τ)`. None of the four has a conclusion of that shape, so there is
nothing to consider and the proof is complete. You will see the same idea,
"no rule fits", carry the impossibility proof of derivation II.

The split $\Gamma = \Gamma_1 \uplus \Gamma_2$ is defined by four rules that walk
through the context one entry at a time and send each entry left, right, or, if
its type is `Copy`, to both sides:

$$
\dfrac{}{\cdot = \cdot \uplus \cdot}\;\textsf{S-Empty}
\qquad
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2}{\Gamma, x : \tau = (\Gamma_1, x : \tau) \uplus \Gamma_2}\;\textsf{S-Left}
$$

$$
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2}{\Gamma, x : \tau = \Gamma_1 \uplus (\Gamma_2, x : \tau)}\;\textsf{S-Right}
\qquad
\dfrac{\Gamma = \Gamma_1 \uplus \Gamma_2 \qquad \mathsf{Copy}(\tau)}{\Gamma, x : \tau = (\Gamma_1, x : \tau) \uplus (\Gamma_2, x : \tau)}\;\textsf{S-Both}
$$

The dot $\cdot$ is the empty context. Rule S-Both is the whole of Chapter 23 in
one line: the exponential $!$ of linear logic, folded into the splitting
operation instead of being a type constructor. Rust makes the same choice:
`Copy` is a property of a type, not a wrapper around it. The Lean definition
transcribes the four rules, with contexts as lists whose head is the most recent
entry:

```lean
{{#include ../../code/lean/Book/Ch28/Typing.lean:ctx}}
```

```lean
{{#include ../../code/lean/Book/Ch28/Typing.lean:split}}
```

A type checker should not try all the ways to split a context: there are up to
three choices per variable, so $3^n$ splits of a context with $n$ variables. The crate instead decides by looking at the two
subterms. A variable goes to the subterm that mentions it; a variable that both
subterms mention must be `Copy`, and goes to both; otherwise the split fails, and
the failure *is* the type error:

```rust
{{#include ../../code/rust/crates/borrowck/src/check.rs:split}}
```

The parameter `bound` handles rebinding. In
$\mathsf{let}\ (x, n) = e_1\ \mathsf{in}\ e_2$ an occurrence of $x$ inside
$e_2$ refers to the new $x$, so it must not pull the old $x$ into $e_2$'s part
of the context. A variable that neither side uses can go to either side: rule
T-Var below accepts extra variables in the context, and that is weakening.

## The typing rules

The judgment of the calculus is

$$
\Delta;\ \Gamma \vdash e : \tau
$$

read "with the lifetimes $\Delta$ in scope and the variables $\Gamma$, the term $e$
has type $\tau$". $\Delta$ is a list of lifetime names, Rust's `<'a, 'b>`;
$\Gamma$ is an affine context. Two conventions keep the rules short. First,
$\Gamma, x : \tau$ is only written when $x$ is not already in $\Gamma$; you can
always rename a bound variable to make this true. (Rebinding an owner after a
borrow, as in the `let` above, is allowed: by then the old $x$ has been consumed
and is no longer in the context.) Second, $\Gamma_1 \uplus \Gamma_2$ in the
conclusion of a rule means "any context that splits into $\Gamma_1$ and
$\Gamma_2$". There are thirteen rules. As in Chapter 1, they are a *model*:
Rust has no official formal semantics, and these rules describe a fragment of
what the compiler enforces, in a simplified form.

### The affine core

$$
\dfrac{(x : \tau) \in \Gamma}{\Delta;\ \Gamma \vdash x : \tau}\;\textsf{T-Var}
\qquad
\dfrac{}{\Delta;\ \Gamma \vdash n : \mathsf{Int}}\;\textsf{T-Int}
\qquad
\dfrac{}{\Delta;\ \Gamma \vdash () : \mathsf{Unit}}\;\textsf{T-Unit}
$$

$$
\dfrac{\Delta;\ \Gamma_1 \vdash e_1 : \tau_1 \qquad \Delta;\ \Gamma_2 \vdash e_2 : \tau_2}{\Delta;\ \Gamma_1 \uplus \Gamma_2 \vdash (e_1, e_2) : \tau_1 \otimes \tau_2}\;\textsf{T-Pair}
$$

$$
\dfrac{\Delta;\ \Gamma_1 \vdash e_1 : \tau_1 \qquad \Delta;\ \Gamma_2, x : \tau_1 \vdash e_2 : \sigma}{\Delta;\ \Gamma_1 \uplus \Gamma_2 \vdash \mathsf{let}\ x = e_1\ \mathsf{in}\ e_2 : \sigma}\;\textsf{T-Let}
$$

$$
\dfrac{\Delta;\ \Gamma_1 \vdash e_1 : \tau_1 \otimes \tau_2 \qquad \Delta;\ \Gamma_2, x : \tau_1, y : \tau_2 \vdash e_2 : \sigma}{\Delta;\ \Gamma_1 \uplus \Gamma_2 \vdash \mathsf{let}\ (x, y) = e_1\ \mathsf{in}\ e_2 : \sigma}\;\textsf{T-LetPair}
$$

$$
\dfrac{\Delta;\ \Gamma \vdash e : \tau}{\Delta;\ \Gamma \vdash \mathsf{new}\ e : \mathsf{Box}\,\tau}\;\textsf{T-New}
\qquad
\dfrac{\Delta;\ \Gamma \vdash e : \tau}{\Delta;\ \Gamma \vdash \mathsf{drop}\ e : \mathsf{Unit}}\;\textsf{T-Drop}
$$

These are Chapter 22's rules, with the moves and drops that Part V explained.

- **T-Var**, **T-Int** and **T-Unit** are the leaves. They accept any other
  variables in $\Gamma$, which is how weakening enters the system: a value that
  is never used is fine. (In our calculus an unused owner is *leaked*, never
  freed, which is safe; Chapter 24 explained why Rust can afford leaks, and a
  real compiler would insert the drop for you.)
- **T-Pair**, **T-Let** and **T-LetPair** split the context between their two
  premises. A variable of a non-`Copy` type is therefore used by at most one of
  them. This is the rule behind E0382: in `let c = b in (b, c)`, both the
  right-hand side and the body need `b`, and `Box Int` is not `Copy`.
- **T-LetPair** is the only way to take a pair apart. It consumes the pair once
  and binds both components, which is how the result of a borrow is unpacked.
- **T-New** allocates, Rust's `Box::new`. **T-Drop** consumes a value of any
  type, Rust's `std::mem::drop`; at run time it frees the locations the value
  owns.

### Using references

$$
\dfrac{\Delta;\ \Gamma \vdash e : \&^{\kappa}\,\tau \qquad \mathsf{Copy}(\tau)}{\Delta;\ \Gamma \vdash {*e} : \tau}\;\textsf{T-Deref}
\qquad
\dfrac{\Delta;\ \Gamma_1 \vdash e_1 : \&^{\kappa}\mathsf{mut}\,\tau \qquad \Delta;\ \Gamma_2 \vdash e_2 : \tau}{\Delta;\ \Gamma_1 \uplus \Gamma_2 \vdash {*e_1} := e_2 : \mathsf{Unit}}\;\textsf{T-Assign}
$$

Rule **T-Deref** reads through a shared reference. Its second premise matters:
reading `*e` produces a copy of the value behind the reference while the original
stays where it is, so the value must be duplicable. Without $\mathsf{Copy}(\tau)$
you could read a $\mathsf{Box}\,\mathsf{Int}$ out of a shared reference and end
up with two owners of one location. Rust reports exactly this situation as
E0507, "cannot move out of `*s` which is behind a shared reference".

Rule **T-Assign** writes through a mutable reference, and only through a mutable
one: there is no rule that assigns through $\&^{\kappa}\,\tau$, which is why
`*s = 1` with `s: &i32` is E0594. The two premises split the context, so the
reference and the new value cannot share a non-`Copy` variable. At run time the
old value is dropped, which is what Rust's `*r = v` does: an assignment to an
initialized place runs the old value's destructor first. (A purely affine
calculus would rather use a *swap* that returns the old value, Rust's
`std::mem::replace`; dropping is closer to what you write every day.)

### Borrowing

Now the three rules that go beyond affine logic:

$$
\dfrac{\Delta;\ \Gamma_1 \vdash e_1 : \mathsf{Box}\,\tau \qquad \Delta, \alpha;\ \Gamma_2, y : \&^{\alpha}\,\tau \vdash e_2 : \sigma \qquad \alpha \notin \Delta \qquad \alpha \notin \mathrm{flv}(\sigma)}{\Delta;\ \Gamma_1 \uplus \Gamma_2 \vdash \mathsf{borrow}\ y = \&^{\alpha} e_1\ \mathsf{in}\ e_2 : \mathsf{Box}\,\tau \otimes \sigma}\;\textsf{T-Borrow}
$$

$$
\dfrac{\Delta;\ \Gamma_1 \vdash e_1 : \mathsf{Box}\,\tau \qquad \Delta, \alpha;\ \Gamma_2, y : \&^{\alpha}\mathsf{mut}\,\tau \vdash e_2 : \sigma \qquad \alpha \notin \Delta \qquad \alpha \notin \mathrm{flv}(\sigma)}{\Delta;\ \Gamma_1 \uplus \Gamma_2 \vdash \mathsf{borrow}\ y = \&^{\alpha}\mathsf{mut}\ e_1\ \mathsf{in}\ e_2 : \mathsf{Box}\,\tau \otimes \sigma}\;\textsf{T-BorrowMut}
$$

$$
\dfrac{\Delta;\ \Gamma_1 \vdash e_1 : \&^{\kappa}\mathsf{mut}\,\tau \qquad \Delta, \alpha;\ \Gamma_2, y : \&^{\alpha}\mathsf{mut}\,\tau \vdash e_2 : \sigma \qquad \alpha \notin \Delta \qquad \alpha \notin \mathrm{flv}(\sigma)}{\Delta;\ \Gamma_1 \uplus \Gamma_2 \vdash \mathsf{borrow}\ y = \&^{\alpha}\mathsf{mut}\,{*e_1}\ \mathsf{in}\ e_2 : \&^{\kappa}\mathsf{mut}\,\tau \otimes \sigma}\;\textsf{T-Reborrow}
$$

The three rules have the same shape, so let us read T-BorrowMut premise by
premise, together with the Rust it models:

```rust,ignore
let mut owner: Box<T> = ...;
let result = {
    let y = &mut *owner;   // 'α starts here
    body                   // uses y; must not use `owner`
};                         // 'α ends here; `owner` is usable again
```

1. **$\Delta;\ \Gamma_1 \vdash e_1 : \mathsf{Box}\,\tau$: the owner is
   consumed.** The owner gets its own part $\Gamma_1$ of the context. Because of
   the split, a non-`Copy` variable used to produce the owner (usually the owner
   variable itself) is not available to the body. This premise is the formal
   reason why you cannot touch `owner` while it is mutably borrowed, and it is
   pure affine bookkeeping.
2. **$\Delta, \alpha;\ \Gamma_2, y : \&^{\alpha}\mathsf{mut}\,\tau \vdash e_2 : \sigma$:
   the body gets the reference.** The body is checked with the rest of the
   context, one more variable $y$ of reference type, and one more lifetime
   $\alpha$ in scope. Since $\&^{\alpha}\mathsf{mut}\,\tau$ is not `Copy`, the
   body can use $y$ at most once; to write through it twice, the body must
   reborrow it, as derivation I will show.
3. **$\alpha \notin \Delta$: the lifetime is fresh.** The borrow introduces a
   new region, distinct from every lifetime already in scope, and binds it for
   the duration of the body. In Rust you never name this lifetime; the compiler
   invents one for every borrow expression.
4. **$\alpha \notin \mathrm{flv}(\sigma)$: the escape check.** The type of the
   body's result must not mention $\alpha$. A value of type $\sigma$ is what
   survives the borrow, and if $\sigma$ mentioned $\alpha$ it could contain a
   reference created by this borrow, still pointing at the location after the
   owner is back in charge of it and free to drop it. This is the premise that
   rejects a dangling reference.
5. **The conclusion $\mathsf{Box}\,\tau \otimes \sigma$: the owner comes back.**
   Ownership was lent, not given away.

T-Borrow differs only in the kind of reference the body receives, a shared one,
which the body may copy freely by rule S-Both. T-Reborrow differs in what is
lent: not an owner but a mutable reference $\&^{\kappa}\mathsf{mut}\,\tau$, and
what comes back is that same reference, *with its original lifetime* $\kappa$.
The new reference lives for the fresh $\alpha$, which is introduced inside the
scope of $\kappa$ and therefore shorter: the outlives relation of Chapter 26
holds by construction, which is why our calculus can do without explicit
outlives constraints. The figure below shows the shape that the three rules share.

![The anatomy of rule T-BorrowMut. The context is split; the owner's part is consumed and lends a reference to the body; the body runs under a fresh lifetime; the escape check filters the body's result; the owner comes back beside it. Blue marks affine bookkeeping, red the region apparatus.](../images/ch28-borrow-rule.svg)

Which premises are affine and which are not? The question matters for the
question of this book, so here is the tally:

| Ingredient | Mechanism | Affine? |
|---|---|---|
| $\Gamma_1 \uplus \Gamma_2$ | context splitting | yes |
| owner consumed by the first premise | affine use | yes |
| owner returned in the conclusion | the lend-and-return shape | neutral |
| $\&^{\alpha}\mathsf{mut}\,\tau$ not `Copy` | no contraction | yes |
| $\&^{\alpha}\,\tau$ is `Copy` | contraction restored | no: the opposite |
| $\alpha$ fresh and scoped to the body | region binding | no |
| $\alpha \notin \mathrm{flv}(\sigma)$ | escape check | no |

Half of the ingredients are affine typing; the other half are a region system.
Keep this table in mind for Chapter 33.

### The rules in Lean and in Rust

In Lean the judgment is an inductive relation, one constructor per rule
(`code/lean/Book/Ch28/Typing.lean`):

```lean
{{#include ../../code/lean/Book/Ch28/Typing.lean:has_type}}
```

Compare a constructor with its rule. The split, written $\Gamma_1 \uplus \Gamma_2$
in the conclusion on paper, is a premise `Split Γ Γ₁ Γ₂`. The convention that a
context is only extended with a new variable becomes explicit premises such as
`y ∉ dom Γ₂` (and `x ≠ y` for a pair pattern): a proof assistant does not accept
conventions, so everything that the paper leaves implicit must be written down.
`α :: Δ` is $\Delta, \alpha$, and `α ∉ σ.lfts` is the escape check.

In the crate, the three borrow rules share one function. It follows the
premises in order: freshness, split, the owner, the body with the new lifetime
and variable, and the escape check last, because only then is $\sigma$ known:

```rust
{{#include ../../code/rust/crates/borrowck/src/check.rs:check_borrow}}
```

Every rule of the calculus is *syntax-directed*: for each form of term exactly one
rule can conclude it, so the checker never searches. When it succeeds, it
returns a `Derivation`, a tree of rule applications with their conclusions and
side conditions:

```rust
{{#include ../../code/rust/crates/borrowck/src/check.rs:derivation}}
```

## Operational semantics

A type system is only as good as the promise it keeps, so we need to say what
programs *do*. The semantics runs terms against a store, and its central device
is a **loan state** for every location.

**Values** are integers, unit, pairs of values and three kinds of pointer:

$$
v, w \;::=\; n \mid () \mid (v_1, v_2) \mid \mathsf{own}\,\ell \mid \mathsf{shr}\,\ell \mid \mathsf{uniq}\,\ell
$$

$\mathsf{own}\,\ell$ is the value of an owner, $\mathsf{shr}\,\ell$ of a shared
reference and $\mathsf{uniq}\,\ell$ of a mutable one, each pointing to a
location $\ell$. At run time there are no lifetimes: references are plain
pointers, exactly as in compiled Rust.

**The store** $S$ maps each allocated location to its contents and its loan
state. We write $S(\ell) = v^{m}$ when $\ell$ holds $v$ in state $m$, where
$m$ is $\mathsf{none}$ (not lent), $\mathsf{shared}$ (lent through a shared
borrow) or $\mathsf{mut}$ (lent through a mutable borrow). The loan states play
no part in the computation itself; they are the bookkeeping that lets the
semantics *detect* a violation of the aliasing rules.

**A borrow in progress** is a run-time term
$\mathsf{restore}\ w\ \mathsf{after}\ e$: run $e$, then hand back $w$ (the owner,
or the reborrowed reference) next to the result. A configuration
$\langle S;\ e \rangle$ steps to $\langle S';\ e' \rangle$ by these rules:

$$
\dfrac{\ell \notin \mathrm{dom}(S)}{\langle S;\ \mathsf{new}\ v \rangle \longrightarrow \langle S[\ell \mapsto v^{\mathsf{none}}];\ \mathsf{own}\,\ell \rangle}\;\textsf{E-New}
\qquad
\dfrac{S' = \mathrm{free}(S, v)}{\langle S;\ \mathsf{drop}\ v \rangle \longrightarrow \langle S';\ () \rangle}\;\textsf{E-Drop}
$$

$$
\dfrac{}{\langle S;\ \mathsf{let}\ x = v\ \mathsf{in}\ e \rangle \longrightarrow \langle S;\ e[v/x] \rangle}\;\textsf{E-Let}
\qquad
\dfrac{}{\langle S;\ \mathsf{let}\ (x, y) = (v_1, v_2)\ \mathsf{in}\ e \rangle \longrightarrow \langle S;\ e[v_1/x, v_2/y] \rangle}\;\textsf{E-LetPair}
$$

$$
\dfrac{S(\ell) = v^{\mathsf{shared}}}{\langle S;\ {*\mathsf{shr}\,\ell} \rangle \longrightarrow \langle S;\ v \rangle}\;\textsf{E-Deref}
\qquad
\dfrac{S(\ell) = w^{\mathsf{mut}} \qquad S' = \mathrm{free}(S[\ell \mapsto v^{\mathsf{mut}}], w)}{\langle S;\ {*\mathsf{uniq}\,\ell} := v \rangle \longrightarrow \langle S';\ () \rangle}\;\textsf{E-Assign}
$$

$$
\dfrac{S(\ell) = v^{\mathsf{none}}}{\langle S;\ \mathsf{borrow}\ y = \&^{\alpha}\,\mathsf{own}\,\ell\ \mathsf{in}\ e \rangle \longrightarrow \langle S[\ell \mapsto v^{\mathsf{shared}}];\ \mathsf{restore}\ \mathsf{own}\,\ell\ \mathsf{after}\ e[\mathsf{shr}\,\ell/y] \rangle}\;\textsf{E-Borrow}
$$

$$
\dfrac{S(\ell) = v^{\mathsf{none}}}{\langle S;\ \mathsf{borrow}\ y = \&^{\alpha}\mathsf{mut}\ \mathsf{own}\,\ell\ \mathsf{in}\ e \rangle \longrightarrow \langle S[\ell \mapsto v^{\mathsf{mut}}];\ \mathsf{restore}\ \mathsf{own}\,\ell\ \mathsf{after}\ e[\mathsf{uniq}\,\ell/y] \rangle}\;\textsf{E-BorrowMut}
$$

$$
\dfrac{S(\ell) = v^{\mathsf{mut}}}{\langle S;\ \mathsf{borrow}\ y = \&^{\alpha}\mathsf{mut}\,{*\mathsf{uniq}\,\ell}\ \mathsf{in}\ e \rangle \longrightarrow \langle S;\ \mathsf{restore}\ \mathsf{uniq}\,\ell\ \mathsf{after}\ e[\mathsf{uniq}\,\ell/y] \rangle}\;\textsf{E-Reborrow}
$$

$$
\dfrac{S(\ell) = w^{m}}{\langle S;\ \mathsf{restore}\ \mathsf{own}\,\ell\ \mathsf{after}\ v \rangle \longrightarrow \langle S[\ell \mapsto w^{\mathsf{none}}];\ (\mathsf{own}\,\ell, v) \rangle}\;\textsf{E-EndBorrow}
$$

$$
\dfrac{}{\langle S;\ \mathsf{restore}\ \mathsf{uniq}\,\ell\ \mathsf{after}\ v \rangle \longrightarrow \langle S;\ (\mathsf{uniq}\,\ell, v) \rangle}\;\textsf{E-EndReborrow}
$$

Here $e[v/x]$ is substitution (Chapter 7), and $\mathrm{free}(S, v)$ removes
from the store every location that $v$ owns: for each $\mathsf{own}\,\ell$ inside
$v$, the location $\ell$, and recursively whatever its contents own. It is
defined only if each of those locations is still allocated and in state
$\mathsf{none}$. One more rule, the congruence rule, lets a step happen inside
a larger term, always in the leftmost subterm that is not yet a value (a pair is
evaluated left to right, a `let` evaluates its right-hand side before its body,
a borrow evaluates its owner before lending it, and a frame runs its body).

The premises above the lines are **guards**. Reading requires the location to
be lent shared; writing requires it to be lent mutably; borrowing an owner
requires it not to be lent; dropping requires everything dropped to be allocated
and not lent. A configuration that is not a value and where no rule applies is
**stuck**, and every way of getting stuck corresponds to a memory-safety bug:
reading or writing freed memory, freeing twice, freeing something that is lent,
writing to a location while it is shared. Being stuck is the calculus's
undefined behavior. A *panic* would be something else entirely: a defined,
orderly way to stop.

Notice what E-Reborrow does to the store: nothing. At run time `&mut *r` is
just `r`; everything a reborrow means happens in the type system.

### The semantics in Rust

The crate's `eval` module implements these rules as a small-step interpreter.
The store is a map from locations to cells with a loan state:

```rust
{{#include ../../code/rust/crates/borrowck/src/eval.rs:store}}
```

and the three borrow rules share one function that checks the guard, updates
the loan state, substitutes a pointer for $y$ and wraps the body in its frame:

```rust
{{#include ../../code/rust/crates/borrowck/src/eval.rs:borrow_step}}
```

Here is a complete well-typed program, closed so that it can run: it allocates
a location, borrows it mutably, writes through two reborrows, gives the owner
back, reads the result through a shared borrow and frees the location
(`crates/borrowck/examples/ch28_run.rs`):

```rust
{{#include ../../code/rust/crates/borrowck/examples/ch28_run.rs:program}}
```

The example checks it and runs it, printing the rule of every step and the store
after it:

```text
{{#include ../../code/rust/output/ch28_run.txt}}
```

Follow the loan state of $\ell_0$ down the right column. It becomes
$\mathsf{mut}$ at step 3, stays $\mathsf{mut}$ through both reborrows (steps 4 to
10: reborrows do not touch the store), goes back to not lent when the mutable
borrow ends at step 12, is lent shared for the read at steps 14 and 15, and the
location disappears at step 18. The figure below draws the same history.

![The loan state of location ℓ0 while the program of ch28_run runs, with the reduction rule that causes each change.](../images/ch28-loans.svg)

## Metatheory

What does the type system guarantee about the semantics? The statements follow
the pattern of Chapter 9, adapted to a store. To type a configuration we need a
**store typing** $\Sigma$ that gives each location the type of its contents,
typing rules for the run-time values
($\mathsf{own}\,\ell : \mathsf{Box}\,\Sigma(\ell)$ and so on), and a notion of a
**well-formed configuration**: the stored values have the types $\Sigma$ says,
and the loan state of every location agrees with the term (a location is lent
exactly when a `restore` frame for it is running, shared or mutable according to
the kind of borrow, and its references occur only inside that frame).

> **Theorem (progress).** If $\langle S;\ e \rangle$ is well formed and
> $\cdot;\ \cdot \vdash_{\Sigma} e : \tau$, then $e$ is a value or
> $\langle S;\ e \rangle \longrightarrow \langle S';\ e' \rangle$ for some $S'$
> and $e'$.
>
> **Theorem (preservation).** If $\langle S;\ e \rangle$ is well formed,
> $\cdot;\ \cdot \vdash_{\Sigma} e : \tau$ and
> $\langle S;\ e \rangle \longrightarrow \langle S';\ e' \rangle$, then
> $\langle S';\ e' \rangle$ is well formed and
> $\cdot;\ \cdot \vdash_{\Sigma'} e' : \tau$ for a store typing $\Sigma'$ that
> agrees with $\Sigma$ on the locations that are still allocated.

Together they give safety: a well-typed closed program never gets stuck, so it
never reads freed memory, never frees twice, never frees what is lent and never
writes to a shared location. We will not prove the two theorems here; a full
proof is long (the run-time typing must record which lifetime lends which
location, so that the escape check can be connected to the values that leave a
frame), and RustBelt, which Chapter 32 describes, proves a much stronger result
for a much larger language. What we can do is see *why* each guard holds in a
well-typed program, because each one rests on a single premise of the rules:

- **Borrowing or dropping an owner finds it not lent.** While $\ell$ is lent,
  its owner $\mathsf{own}\,\ell$ sits inside a `restore` frame, where no rule can
  reach it, and there is no other copy of it because $\mathsf{Box}\,\tau$ is not
  `Copy`. *Affinity.*
- **Reading through $\mathsf{shr}\,\ell$ finds $\ell$ lent shared.** A shared
  reference is created inside a frame and cannot leave it, because its type
  mentions the borrow's lifetime and the escape check forbids exactly that.
  *Regions.*
- **Writing through $\mathsf{uniq}\,\ell$ finds $\ell$ lent mutably.** The same
  argument, for mutable references.
- **No location is freed twice.** Only an owner frees, and owners cannot be
  duplicated. *Affinity again.*

Here is the division of labor in one table:

| Guarantee | Comes from |
|---|---|
| no double free | $\mathsf{Box}\,\tau$ is not `Copy` (affinity) |
| a mutable reference is unique | $\&^{\kappa}\mathsf{mut}\,\tau$ is not `Copy` (affinity) |
| the owner is untouchable while lent | the borrow consumes it until its body ends (affinity plus scoping) |
| no dangling reference | the escape check (regions) |
| lifetimes do not get confused | freshness (regions) |

The semantics is deliberately coarse, and it is worth knowing where. A reborrow
does not change the store, so if an ill-typed program let a reborrowed reference
escape, two $\mathsf{uniq}\,\ell$ pointers would coexist and the machine would not
notice. Semantic models of Rust such as Stacked Borrows and Tree Borrows, which
Chapter 32 describes, tag every pointer to catch exactly such cases.

The guards are not decoration. The `ch28_go_wrong` example takes two programs
that the checker rejects and runs them anyway:

```rust
{{#include ../../code/rust/crates/borrowck/examples/ch28_go_wrong.rs:programs}}
```

```text
{{#include ../../code/rust/output/ch28_go_wrong.txt}}
```

The first program lets a shared reference escape its borrow, drops the owner and
reads through the reference: a use after free, which the machine catches as a
failed guard. The checker had rejected it with the escape check. The second is
derivation II, which we are about to study: the machine gets stuck when the body
tries to lend $\ell_0$ mutably while it is lent shared.

## Worked derivation I: a `&mut` reborrow

Here is a puzzle that every Rust programmer meets eventually. A `&mut i32` is not
`Copy`; by everything Part V said, it is an affine value that can be used at most
once. Yet this compiles (`code/rust/examples/ch28_reborrows.rs`):

```rust
{{#include ../../code/rust/examples/ch28_reborrows.rs:implicit}}
```

The resolution is that `set(r, 1)` does not pass `r`. Because `set` expects a
`&mut i32`, the compiler inserts an **implicit reborrow** and passes `&mut *r`, a
new reference that lives only for the call. During the call `r` is lent; after
it, `r` is usable again. Written out by hand, with one block per reborrow:

```rust
{{#include ../../code/rust/examples/ch28_reborrows.rs:explicit}}
```

Inlining `set` turns this into a term of the calculus. In the crate's syntax, as
a program whose parameters form the initial context
(`crates/borrowck/examples/ch28_borrowck.rs`):

```rust
{{#include ../../code/rust/crates/borrowck/examples/ch28_borrowck.rs:twice}}
```

We want to derive $\alpha;\ r : M_{\alpha} \vdash \mathit{twice} : \mathsf{Unit}$,
where $M_{\kappa}$ abbreviates $\&^{\kappa}\mathsf{mut}\,\mathsf{Int}$ and we
write $\alpha$ for `'a`, $\beta_1$ and $\beta_2$ for `'b1` and `'b2`. Call the
two reborrows $E_1$ and $E_2$.

**Step 1: the body of the first reborrow.** In the lifetime context
$\Delta_1 = \alpha, \beta_1$, the body writes `1` through $y_1$. Rule T-Assign
splits the context $y_1 : M_{\beta_1}$, giving $y_1$ to the reference and
nothing to the literal:

$$
\mathcal{D}_1 \;=\; \dfrac{\dfrac{}{\Delta_1;\ y_1 : M_{\beta_1} \vdash y_1 : M_{\beta_1}}\;\textsf{T-Var} \qquad \dfrac{}{\Delta_1;\ \cdot \vdash 1 : \mathsf{Int}}\;\textsf{T-Int}}{\Delta_1;\ y_1 : M_{\beta_1} \vdash {*y_1} := 1 : \mathsf{Unit}}\;\textsf{T-Assign}
$$

**Step 2: the reborrow.** Rule T-Reborrow, with $\kappa := \alpha$,
$\tau := \mathsf{Int}$ and $\sigma := \mathsf{Unit}$, splits $r : M_{\alpha}$
by giving $r$ to the reborrowed expression and nothing to the body:

$$
\dfrac{\dfrac{}{\alpha;\ r : M_{\alpha} \vdash r : M_{\alpha}}\;\textsf{T-Var} \qquad \mathcal{D}_1 \qquad \beta_1 \notin \{\alpha\} \qquad \beta_1 \notin \mathrm{flv}(\mathsf{Unit})}{\alpha;\ r : M_{\alpha} \vdash E_1 : M_{\alpha} \otimes \mathsf{Unit}}\;\textsf{T-Reborrow}
$$

All four premises hold: the first by T-Var, the second is $\mathcal{D}_1$, the
lifetime $\beta_1$ is fresh, and the body's type $\mathsf{Unit}$ mentions no
lifetime at all, so the escape check passes.

Now look at the conclusion. The type is $M_{\alpha} \otimes \mathsf{Unit}$: the
reborrow **consumed** $r$, exactly as affinity demands, and **produced a new
reference at the same lifetime** $\alpha$, as the first component of the pair.
So `r` really is used only once. What makes `set(r, 1); set(r, 2);` legal is not
that `&mut` can be duplicated, but that each reborrow hands back a fresh binding
of the same type. Rust hides the rebinding; the calculus makes it a `let`.

**Step 3: unpack and repeat.** Rule T-LetPair unpacks the pair into
$r_1 : M_{\alpha}$ and $u_1 : \mathsf{Unit}$. The second premise's context,
$r_1 : M_{\alpha}, u_1 : \mathsf{Unit}$, contains a reference of exactly the
same type as the original $r$, so Steps 1 and 2 apply again with $r_1$,
$\beta_2$ and $y_2$, giving
$\alpha;\ r_1 : M_{\alpha} \vdash E_2 : M_{\alpha} \otimes \mathsf{Unit}$. A
second T-LetPair unpacks that pair, and the final $()$ is typed by T-Unit, whose
context $u_1, r_2, u_2$ is simply ignored (weakening). The derivation is
complete.

Here is the same derivation as the crate prints it. Each line is a rule
application; the lines below a rule list its side conditions (the split and, for
borrows, freshness and the escape check), followed by its premises:

```text
{{#include ../../code/rust/output/ch28_borrowck.txt:1:24}}
```

### What each side condition bought

Every premise of T-Reborrow rules out a real bug. Take them away one at a time:

| Ingredient | What would go wrong without it |
|---|---|
| the split $\Gamma_1 \uplus \Gamma_2$ | the body could use $r$ as well as $y_1$: two live `&mut` to one location |
| $\neg\mathsf{Copy}(M_{\beta_1})$ | the body could duplicate $y_1$ |
| $\beta_1$ fresh | two regions could share a name; here that only makes the escape check stricter, but the substitution lemmas of a full proof need distinct names |
| $\beta_1 \notin \mathrm{flv}(\sigma)$ | the body could return $y_1$, which would then alias the returned $r_1$ |
| the conclusion returns $M_{\alpha}$ | one reborrow would consume $r$ for good, and the second write would be rejected |

The last row is not hypothetical: Rust behaves exactly like that when it does
not insert the reborrow. The compiler inserts implicit reborrows only where the
expected type is known to be a mutable reference. When the parameter is generic,
the argument is simply moved:

```rust
{{#include ../../code/rust/compile_fail/ch28_no_reborrow.rs:no_reborrow}}
```

```text
{{#include ../../code/rust/compile_fail/ch28_no_reborrow.stderr}}
```

Read the error with the calculus in mind: "move occurs because `r` has type
`&mut i32`, which does not implement the `Copy` trait". Without a reborrow,
`&mut` is affine, and the compiler's suggestion is literally rule T-Reborrow:
"consider creating a fresh reborrow of `r` here". With the explicit reborrows,
the generic version compiles (`twice_generic` in the example). This is good
empirical evidence that the account in this chapter is the right one.

### The borrow rules as Rust functions

You can write the three borrow rules as Rust functions, and their signatures say
everything the rules say:

```rust
{{#include ../../code/rust/examples/ch28_reborrows.rs:combinators}}
```

Each function takes the owner (or the reference) by value: it is consumed. The
body is a closure that receives the new reference. The higher-ranked bound
`for<'a>` (Chapter 12) says that the closure must work for *every* lifetime
`'a`, which makes `'a` fresh: the closure cannot assume anything about it. The
result type `S` is a type parameter of the outer function, chosen before `'a`
is even in scope, so `S` cannot mention `'a`: that is the escape check, enforced
by Rust's own type checker. (Try `lend(b, |y| y)`: rustc rejects the closure,
because returning `y` would require its lifetime to outlive the closure call.)
And the owner comes back in the result pair. With these functions, derivation I
can be transcribed into Rust term by term, and it compiles:

```rust
{{#include ../../code/rust/examples/ch28_reborrows.rs:twice_calculus}}
```

```text
{{#include ../../code/rust/output/ch28_reborrows.txt}}
```

### Derivation I in Lean

In Lean a derivation is a proof term, built from the constructors of `HasType`
(`code/lean/Book/Ch28/Derivations.lean`). First the term itself and the
abbreviation $M_{\kappa}$:

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:abbrev_m}}
```

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:twice}}
```

Then $\mathcal{D}_1$, which is one line: rule T-Assign (`.assign`) applied to
the split that sends `y1` left (`.left .nil`), a T-Var leaf whose premise
`lookup [("y1", M "b1")] "y1" = some (M "b1")` holds by computation (`rfl`), and
a T-Int leaf (`.lit`):

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:d1}}
```

The first reborrow is rule T-Reborrow applied to its six premises, in the order
of the constructor. The side conditions are decidable facts about concrete
strings and lists, so `decide` proves them by evaluation, as it did in Chapter 1:

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:e1}}
```

The second reborrow is the same derivation for `r1` and `'b2`, and the whole
derivation puts the pieces together with two T-LetPair steps. The second split,
`.left (.right .nil)`, sends `r1` to the reborrow and `u1` to the body:

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:e2}}
```

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:twice_typed}}
```

Lean checks every step: if a split sent a variable to the wrong side, or a
lifetime were not fresh, the term would not type-check and the theorem would not
exist.

## Worked derivation II: the aliasing bug

The classic bug: take a reference into a vector, push onto the vector (which may
reallocate its buffer), then use the reference.

```rust
{{#include ../../code/rust/compile_fail/ch28_aliasing_bug.rs:aliasing_bug}}
```

```text
{{#include ../../code/rust/compile_fail/ch28_aliasing_bug.stderr}}
```

In the calculus, the vector is an owner `v : Box Int`, the reference `first` is
a shared borrow `f` of `v` (of the whole vector rather than of its first
element, a simplification), and `v.push(4)` is a write through a mutable borrow
of `v`. The use of `first` after the push puts the push inside the shared
borrow's body:

```rust
{{#include ../../code/rust/crates/borrowck/examples/ch28_borrowck.rs:aliasing}}
```

**Why no derivation exists.** The term is a shared borrow, and since the rules
are syntax-directed, only T-Borrow can conclude it. T-Borrow requires the context
$v : \mathsf{Box}\,\mathsf{Int}$ to be split into $\Gamma_1$, for the owner, and
$\Gamma_2$, for the body. The owner is the variable $v$, and the only rule for a
variable is T-Var, so $v$ must be in $\Gamma_1$. The body contains
$\mathsf{borrow}\ m = \&^{\beta}\mathsf{mut}\ v\ \mathsf{in}\ \dots$, whose owner
is $v$ again, so by the same reasoning $v$ must be in the body's context, which
is built from $\Gamma_2$. The variable would have to be on both sides, and rule
S-Both allows that only if $\mathsf{Copy}(\mathsf{Box}\,\mathsf{Int})$, which no
rule concludes. There is no split, so there is no derivation. The figure below
draws the argument.

![Derivation II fails at the very first rule: the context v : Box Int would have to go to both premises of T-Borrow, which requires Copy(Box Int).](../images/ch28-failed-split.svg)

The crate reports the failed split, naming the variable, the rule and the two
premises that both need it:

```text
{{#include ../../code/rust/output/ch28_borrowck.txt:26:31}}
```

rustc's message speaks of *borrows*: "cannot borrow `v` as mutable because it is
also borrowed as immutable". The calculus's reason is a failed *context split*.
They agree because rule T-Borrow consumes the owner for the whole duration of
the borrow. You can watch the same agreement inside rustc by transcribing the
term with the `lend` functions from derivation I:

```rust
{{#include ../../code/rust/compile_fail/ch28_aliasing_lend.rs:aliasing_lend}}
```

```text
{{#include ../../code/rust/compile_fail/ch28_aliasing_lend.stderr:1:12}}
```

Now rustc reports E0382, use of a moved value: the owner was moved into `lend`,
and the closure (the body) needs it again. This is the affine phrasing of the
same bug, and it is exactly the calculus's phrasing.

**What non-lexical lifetimes changed.** Delete the `println!` from the Rust
program and rustc accepts it, because `first` is no longer used after the push:
its borrow is dead. Our calculus would still reject the corresponding term,
because a lexical borrow lasts for its whole body. To make the program typable
you narrow the borrow by hand, reading before pushing, and both the calculus and
Rust accept the result:

```rust
{{#include ../../code/rust/examples/ch28_reborrows.rs:read_then_push}}
```

Closing this gap is why the real borrow checker is a dataflow analysis rather
than a type system (Chapter 29).

### Derivation II in Lean: proving that no derivation exists

Lean lets us turn "there is no derivation" into a theorem. The statement says:
for every lifetime context `Δ` and every type `τ`, there is no proof of
`HasType Δ [("v", .box .int)] aliasing τ`.

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:aliasing}}
```

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:aliasing_untypable}}
```

The proof is the paper argument, one inversion at a time. `intro h` assumes a
derivation `h` and aims for a contradiction. `cases h` asks Lean which
constructors of `HasType` could have produced `h`. Lean compares the conclusion
of every constructor with `HasType Δ [("v", .box .int)] aliasing τ`, discards
those whose term does not match (only `.borrow` produces a shared borrow), and
gives us the premises of the one that is left: the split `hs`, the derivation `hv`
of the owner, and the derivation `hbody` of the body.

`cases hs` does the same for the split of the one-entry context. S-Empty cannot
match a non-empty list, so three cases remain, one for each place `v` can go:

- **Both sides** (`both`): the premise `hc` claims that `Box Int` is `Copy`, and
  `not_copy_box` refutes it.
- **Right** (`right`): the owner's context is empty. (The inner `cases hs`
  splits the rest of the context, which is empty, so it has a single case.)
  `hv.var_mem` is a small lemma from `Typing.lean`, the inversion of T-Var: a
  variable that has a type is in the context. Here it says `"v" ∈ dom []`, and
  `simp` reduces that to `False`.
- **Left** (`left`): after the same inner `cases hs`, the body's context is
  `[("f", &'a Int)]`. Two more inversions open the body: it is a `let`-pair (`.letPair`), whose right-hand
  side is a mutable borrow (`.borrowMut`), whose owner is the variable `v`. Its
  context `Γ₅` is a part of a part of `[f]` (each split produces sublists of its
  context, a lemma called `Split.sublist`), so `v` would be in `dom [f]`, and
  `simp` sees that `"v" ∈ ["f"]` is false.

Every branch ends in a contradiction, so `h` cannot exist. There is also a
shorter route, through the metatheorem of the next section: `v` occurs twice in
the term, and the theorem says that a non-`Copy` variable occurs at most once in
any well-typed term:

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:aliasing_corollary}}
```

### The escape check, in Lean

The usage theorem explains derivation II, but not every rejection is affine. The
dangling program of the `ch28_go_wrong` example reduces to its core,
$\mathsf{borrow}\ y = \&^{\alpha} b\ \mathsf{in}\ y$, which uses $b$ only once.
It is rejected by the escape check alone, and the Lean proof finds exactly that
premise:

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:escape}}
```

After inverting T-Borrow, the body `y` must be typed by T-Var, so its type is
the type of `y` in the body's context, `&'a τ'` for the owner's content type
`τ'`. `simp [lookup] at hl` computes the lookup and turns `hl` into the
equation `Ty.ref "a" τ' = σ`, and `subst` replaces σ everywhere. The escape
check premise `hesc` now reads `"a" ∉ (Ty.ref "a" τ').lfts`, and `simp` unfolds
`lfts` and finds `"a"` at the head of the list. The usage theorem has nothing to
say here: `b` is used once.

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:escape_occ}}
```

In real Rust, the same bug (keep a reference to the box, drop the box, use the
reference) is E0505:

```text
{{#include ../../code/rust/compile_fail/ch28_drop_while_borrowed.stderr}}
```

## The metatheorem: a mutable reference is used at most once

We close the formal part with a real theorem about all derivations at once, the
calculus's version of Chapter 22's usage theorem. If a variable has a type that
is not `Copy` (an owner or a mutable reference) then it occurs at most once in
any well-typed term. "Occurs" means *free* occurrences, counted by a recursive
function on terms that skips the scope of any binder for the same name:

```lean
{{#include ../../code/lean/Book/Ch28/Syntax.lean:occ}}
```

Two lemmas carry the proof. The first is about splits, and it is the formal core
of the whole chapter: a non-`Copy` variable goes to exactly one side.

```lean
{{#include ../../code/lean/Book/Ch28/Typing.lean:split_non_copy}}
```

The proof is by induction on the split. In each step case it asks whether the
entry just handled is `x` itself (`by_cases hxy : x = y`). If it is, then in the
cases `left` and `right` it went to one side, and the other side cannot contain
`x` because the context has no repeated variables (`hnd`, the `Nodup` hypothesis)
and each side is a sublist of the context. In the case `both` the entry must be
`Copy`, contradicting `hσ`. If the entry is some other variable, the induction
hypothesis applies to the rest of the context, and `lookup_cons_ne` (looking up
`x` past a different variable) moves the conclusion back up.

The second lemma says that a variable absent from the context does not occur in a
well-typed term (`HasType.occ_eq_zero` in `Typing.lean`). It is a
straightforward induction on the derivation, and we use it without showing it.

Here is the theorem. The first cases are the easy ones:

```lean
{{#include ../../code/lean/Book/Ch28/Typing.lean:usage_simple}}
```

The proof is by induction on the derivation `h`, `generalizing x` so that the
induction hypothesis can be used for whatever variable a premise needs.

- **T-Var**: the term is a variable `y`, and `occ` is `1` if `x = y` and `0`
  otherwise. `simp only [Term.occ]` unfolds the definition, `split` considers
  the two branches of the `if`, and `omega` (the arithmetic decision procedure
  you met in Chapter 2) checks `1 ≤ 1` and `0 ≤ 1`.
- **T-Int and T-Unit**: there are no variables at all.
- **T-New, T-Drop, T-Deref**: one premise with the same context; the induction
  hypothesis is exactly the goal.

The two-premise rules without binders, T-Pair and T-Assign, are where the split
lemma does its work:

```lean
{{#include ../../code/lean/Book/Ch28/Typing.lean:usage_pair}}
```

`rcases` takes apart the disjunction from `Split.non_copy`. If `x` went left,
the induction hypothesis for the left premise bounds its occurrences in `e₁` by
1 (the left part has no repeated variables either, being a sublist), and
`occ_eq_zero` says it does not occur in `e₂` at all. `omega` adds the two
facts. If `x` went right, the roles are swapped.

The rules with a binder (T-Let and the three borrow rules, which all bind a
variable in their second premise) need one more observation:

```lean
{{#include ../../code/lean/Book/Ch28/Typing.lean:usage_binder}}
```

If `x` went to the first premise, the body either rebinds `x` (then `occ` counts
nothing there, by definition) or does not mention it at all (`occ_eq_zero`,
since `x` is neither in `Γ₂` nor the bound variable). If `x` went to the body,
then `x` is different from the bound variable `y`, because `y ∉ dom Γ₂` while
`x` is in `Γ₂` (`ne_of_mem_dom`). So the body's context `(y, _) :: Γ₂` still has
no repeated variables, looking up `x` in it finds the same type, and the
induction hypothesis applies. T-LetPair, not shown, is the same argument with two
bound variables. The theorem holds for all derivations, whatever the term.

The case this chapter cares about is a corollary:

```lean
{{#include ../../code/lean/Book/Ch28/Typing.lean:ref_mut_once}}
```

and the contrast with shared references is two small examples: a shared
reference goes to both sides of a pair by S-Both, while a mutable one makes the
pair untypable.

```lean
{{#include ../../code/lean/Book/Ch28/Derivations.lean:copy_split}}
```

Note what the theorem does *not* say. It says nothing about lifetimes: the
escape check, freshness and the scoping of borrows play no role in its proof.
The usage theorem is the affine half of the calculus, proved; the region half
needs the semantics, which is why safety needs both.

## Putting it together: a checker for the calculus

The `borrowck` crate is a small pipeline with one module per stage: `parse`
reads a program in the concrete syntax into the types of `syntax`, `check`
builds a derivation or explains which premise fails, and `eval` runs the program
on the abstract machine. The main example prints both worked derivations:

```rust
{{#include ../../code/rust/crates/borrowck/examples/ch28_borrowck.rs:main}}
```

To see the calculus as a whole, here is a suite of programs, each paired with
the rustc error code that the corresponding real Rust program produces (every
one of those was checked against the compiler)
(`crates/borrowck/examples/ch28_suite.rs`):

```rust
{{#include ../../code/rust/crates/borrowck/examples/ch28_suite.rs:programs}}
```

```text
{{#include ../../code/rust/output/ch28_suite.txt}}
```

Read the table row by row and match each verdict to the rule that produced it:

- `twice` and `read_then_push` are the two programs we derived, and `share`
  copies a shared reference by S-Both.
- `aliasing` (E0502), `two_mut` (E0499), `drop_while_borrowed` (E0505) and
  `use_after_move` (E0382) are four different rustc errors, but in the calculus
  they are one error: a non-`Copy` variable needed by both premises of a split.
  The compiler distinguishes them by what the second use does (borrow, borrow
  mutably, move, use after a move); the calculus sees a single structural rule
  missing.
- `dangling` is the escape check, the only region error in the suite.
- `move_out` (E0507) is the $\mathsf{Copy}(\tau)$ premise of T-Deref, and
  `write_shared` (E0594) is the absence of any rule that writes through a shared
  reference.

The Lean relation `HasType` is the specification: it states what a derivation
is, without saying how to find one. The Rust checker is an algorithm that finds
derivations by deciding each split from the subterms. We did not prove the
algorithm sound with respect to the specification (Chapter 3 shows the technique
on a simpler language); the crate's tests and the Lean proofs check the same
derivations from both ends.

## Common confusions

**"A reborrow copies the `&mut`."** It does not, at least not in the type
system. The reborrow consumes the reference and hands it back afterwards, with
the same lifetime, under a new name. At run time it is a pointer copy (rule
E-Reborrow does not touch the store), but statically the original is unusable
while the reborrow lives: that is the split in T-Reborrow.

**"Lifetimes are affine resources."** Nothing in the calculus counts uses of a
lifetime. A lifetime is a name for a region; the rules that mention it
(freshness, the escape check) are about *scope*, not about *multiplicity*. The
shared reference, the paradigm example of a type with a lifetime, is the most
freely duplicable value of the calculus.

**"This is how rustc checks borrows."** No. The calculus is a *specification*,
stricter than today's compiler (it rejects programs that NLL accepts). rustc
runs a dataflow analysis on MIR, which Chapter 29 builds in miniature.

**"Getting stuck is a panic."** A panic is defined behavior: the program stops in
an orderly way, running destructors. Getting stuck means the semantics has no
answer, which corresponds to undefined behavior. The type system rules out the
latter and says nothing about the former.

**"The escape check is about returning references from functions."** That is one
instance (E0515). The check applies to every borrow, and it also rejects a
reference stored in a variable that outlives the borrow (E0597) and, as the
`dangling` program shows, a reference used after the owner is dropped (E0505).

## Summary

- $\lambda^{\mathsf{aff}}_{\mathsf{rgn}}$ combines the affine core of Part V
  (context splitting, `Copy`, drops) with a region system (lexically scoped
  borrows, fresh lifetimes, the escape check) in thirteen syntax-directed typing
  rules.
- A borrow lends its owner and gives it back: its type is
  $\mathsf{Box}\,\tau \otimes \sigma$. Because the owner is consumed by the
  borrow, "no use of the owner while it is borrowed" is just context splitting.
- `Copy` is a predicate that lets a variable go to both sides of a split. Shared
  references are `Copy`; owners and mutable references are not.
- The operational semantics gives every location a loan state; reading, writing,
  borrowing and freeing have guards, and a failed guard is a stuck state, the
  calculus's undefined behavior. Progress and preservation say that well-typed
  programs never get stuck. A reborrow changes nothing at run time.
- Derivation I: `bump(r); bump(r);` works because each implicit reborrow consumes
  `r` and returns a reference of the same type. Without the reborrow (a generic
  parameter), `&mut` is affine and rustc reports E0382.
- Derivation II: the aliasing bug fails at the first rule, because the owner
  would have to go to both premises of T-Borrow and `Box` is not `Copy`. rustc
  calls it E0502; the calculus calls it a failed split.
- In Lean, the rules are an inductive relation, derivations are proof terms,
  impossibility is proved by inversion (`cases`, `nomatch`), and the usage
  theorem proves that a non-`Copy` variable, in particular a mutable reference, is
  used at most once. The escape check is the part of the system that the usage
  theorem cannot explain.

## Exercises

1. Write the term $\mathsf{borrow}\ y = \&^{\alpha}\mathsf{mut}\ b\ \mathsf{in}\ y$
   with $b : \mathsf{Box}\,\mathsf{Int}$ in the crate's syntax and check it.
   Which premise of T-BorrowMut fails? Write a Rust function with the same bug
   and compare rustc's error code with the ones in this chapter.
   *Hint:* the body's type is $\&^{\alpha}\mathsf{mut}\,\mathsf{Int}$; in Rust,
   try returning `&mut *b` from a function that owns the box `b`.

2. Write the complete derivation tree of `read_then_push` from the suite, with
   every split. Then construct it in Lean as a proof of
   `HasType [] [("v", .box .int)] readThenPush .int` for a suitable definition of
   `readThenPush`.
   *Hint:* in the first `let`-pair the variable `v` goes left; in the second,
   `v` goes left and `n` goes right, all the way down to the final `n`. Build
   the derivation from the leaves up, as `twice_typed` does.

3. Add a rule T-DerefMut that reads a `Copy` value through a mutable reference,
   to the crate's checker and to Lean's `HasType`. Does the usage theorem still
   hold? Repair its proof.
   *Hint:* the new constructor has one premise and the same context, so the new
   case of `used_at_most_once` is the same as the case for `deref`. Note that the
   reference is consumed by the read, so reading and then writing needs a
   reborrow.

4. Prove in Lean that
   `borrow y = &'a mut b in (y, y)` has no type in the context `b : Box Int`.
   *Hint:* invert T-BorrowMut with `cases`, then apply
   `HasType.ref_mut_used_at_most_once` to the derivation of the body, whose
   context starts with `("y", .refMut "a" _)`. You need to show that this
   context has no repeated variables: `y` is not in the rest of it (a premise of
   the rule), and the rest is a sublist of `[b]`.

5. Find a program that the checker rejects but that the interpreter runs to a
   value without getting stuck. Does that mean the checker is too strict? What
   would go wrong if you extended the program?
   *Hint:* try `use_after_move` from the suite, made closed with `new`. Look at
   the value it produces: how many owners does location $\ell_0$ have, and what
   would two `drop`s do?

6. Design a *shared reborrow*, `borrow y = &'a *e1 in e2`, which takes a mutable
   reference $e_1 : \&^{\kappa}\mathsf{mut}\,\tau$ and gives the body a shared
   reference $y : \&^{\alpha}\,\tau$ (Rust's `&*r`). Write the typing rule and the
   reduction rule. What loan state does the location need while the shared
   reborrow runs, and what must happen when it ends?
   *Hint:* during the body the location must be readable but not writable, so
   its state must change from $\mathsf{mut}$ to $\mathsf{shared}$ and back. The
   frame must remember which state to restore.
