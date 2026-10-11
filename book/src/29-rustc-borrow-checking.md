# How rustc Really Checks Borrows

Chapter 28 ended with a type system for borrowing: a dozen rules, derivations
that Lean checks, and a proof that the classic aliasing bug has no derivation at
all. It also ended with a confession. Its calculus rejects this program, and the
Rust compiler accepts it:

```rust
{{#include ../../code/rust/examples/ch29_nll_accepts.rs:first_then_push}}
```

The reference `first` is used for the last time on the `println!` line, so by
the time `readings.push(40)` runs, nobody can observe the old buffer through
`first` any more. A borrow that is lexically scoped, as in Chapter 28's calculus
and in Rust before 2018, lasts until the closing brace and makes the `push` an
error. Today's compiler sees that the borrow is *dead* after its last use.

To see that, the compiler must follow the program as a graph: which statements
can run after which, which values may still be used later. This chapter opens
the hood. We follow a function from source text to MIR, the control-flow graph
the borrow checker works on; we build the dataflow analyses that run on it in a
Rust crate that reproduces rustc's error messages; and we prove in Lean the
facts about fixpoints that make those analyses trustworthy. On the way we meet
two-phase borrows, a safe program that the stable borrow checker still
rejects, and Polonius, the reformulation designed to accept it.

**In this chapter you will learn:**

- why rustc's borrow checker is a static analysis rather than a type system, and
  what each kind of checker is good at;
- what MIR is: basic blocks, places, `StorageLive` and `StorageDead`, drops,
  and how to look at the real thing;
- how dataflow analysis works (lattices, transfer functions, the worklist
  algorithm) and how it finds moved values (E0382) and live variables;
- how non-lexical lifetimes compute regions as sets of program points, and how
  loans and their conflicts produce E0499, E0502 and E0506;
- what two-phase borrows are, why `v.push(v.len())` compiles and
  `v.push(v.pop().unwrap())` does not;
- why NLL rejects "problem case #3", and how Polonius' formulation in terms of
  origins and loans accepts it;
- how to prove in Lean that a dataflow solver returns a fixpoint, the least one,
  and always terminates on a finite lattice.

## A type system or an analysis?

Chapter 28's calculus is a type system in the sense of Chapter 3. There is a
judgment, there are inference rules, and a program is accepted when a
derivation exists. The rules are *syntax-directed*: each one looks at one form
of term, and the derivation has the shape of the program's syntax tree. A
borrow is a construct with a body, $\mathsf{borrow}\ y = \&^{\alpha} x\
\mathsf{in}\ e$, and its lifetime is that body. That design has real virtues.
The derivation is a certificate that anybody can check, the rules compose (if
the parts are well typed, so is the whole), and the metatheory is a matter of
induction on derivations, which is what made the Lean proofs of Chapter 28
possible.

rustc's borrow checker works differently. It does not look for a derivation. It
turns the function body into a control-flow graph, computes *facts* at every
point of the graph ("`job` may have been moved", "`first` will be used again",
"the loan of `readings` is still in force"), and reports an error wherever some
point violates a rule. That is a **static analysis**, and in particular a
*dataflow* analysis: facts flow along the edges of the graph until nothing
changes.

| | Type system (Chapter 28) | Analysis (rustc) |
|---|---|---|
| Works on | the syntax tree | the control-flow graph |
| Produces | a derivation | facts at every program point |
| A borrow lasts | its lexical scope | while a reference made from it may be used |
| Rejects when | no derivation exists | some path reaches a conflict |

Both are *conservative*: they reject some programs that would never misbehave,
because deciding exactly which programs misbehave is impossible in general (it
would decide the halting problem). The analysis is conservative in a specific,
well-defined way: it considers every path through the graph as possible,
without evaluating conditions. rustc says so itself, in a note it attaches to
one of its errors:

```rust
{{#include ../../code/rust/compile_fail/ch29_maybe_uninit.rs:maybe_uninit}}
```

```text
{{#include ../../code/rust/compile_fail/ch29_maybe_uninit.stderr}}
```

Read the note at the end. The compiler is not claiming that `warm` can be
false at run time; it is telling you that its reasoning is about *paths*.

What the analysis buys is *flow sensitivity*: the facts can differ from one
point to the next and from one branch to the other, which is exactly what
`first_then_push` needs. What it gives up is the certificate: there is no
derivation to print, and an error message has to reconstruct a story ("borrow
later used here") from a table of facts. Chapter 33 will build on this trade:
the theories of Parts V and VI describe *what* the borrow checker enforces;
*how* it enforces it is the subject of this chapter.

> [!NOTE]
> Everything this chapter says about rustc describes the pinned compiler, Rust
> 1.99, and its documented design. The internals of rustc are not a stable
> interface: names, passes and dump formats change between releases. The ideas
> (MIR, dataflow, regions as sets of points, loans) have been stable for years.

## From source text to MIR

A Rust function goes through several representations before machine code comes
out, and different errors come from different stages:

![The stages of rustc that matter for borrow checking, with the errors each stage reports. The borrow checker runs on MIR, after type checking.](../images/ch29-pipeline.svg)

The **AST** is the syntax tree of Chapter 3, after macro expansion and name
resolution. The **HIR** (high-level intermediate representation) is the AST
with some sugar removed: `for` loops become `loop` plus `match`, `?` and
`if let` become `match`. **Type checking** runs on the HIR: it infers types
(Chapter 13), resolves method calls, and inserts the implicit operations such
as auto-referencing of method receivers. E0308 and E0282 come from here.

Type checking does *not* decide the lifetimes inside a function body. It needs
lifetimes to check signatures and trait bounds, but the lifetime of each borrow
expression inside the body is left open: the type checker records types with the
regions *erased*. The **THIR** (typed HIR) is the fully typed, fully explicit
version of the body, every autoref and deref spelled out; pattern exhaustiveness
(E0004) is checked on it, and it is the input to MIR building.

**MIR** (mid-level intermediate representation) is a control-flow graph, and
the borrow checker runs on it. It gives every region in the body a fresh
inference variable (rustc calls this step *renumbering*), type-checks the MIR
once more to collect constraints between those variables, computes which
variables are live and which places are initialized, solves the region
constraints, and checks every access against the loans in force. After borrow
checking, *drop elaboration* decides how to run the destructors, and the MIR is
optimized and translated to LLVM IR.

### What MIR looks like

Here is a function that moves a `String` on one path only, from
`code/rust/examples/ch29_nll_accepts.rs`:

```rust
{{#include ../../code/rust/examples/ch29_nll_accepts.rs:maybe_archive}}
```

And here is its MIR, exactly as the borrow checker sees it. A nightly compiler
can dump MIR at any stage with the unstable flag `-Zdump-mir`; this listing was
produced by `rustc 1.101.0-nightly (2026-10-08)` with

```sh
rustc +nightly --edition 2024 --emit=metadata \
  -Zdump-mir=maybe_archive -Zdump-mir-dir=mir_dump examples/ch29_nll_accepts.rs
```

taking the file `mir_dump/ch29_nll_accepts.maybe_archive.-------.nll.0.mir` and
removing the source-position comments at the end of each line:

```text
{{#include ../../code/rust/output/ch29_maybe_archive.nll.mir.txt}}
```

Let us read it.

- **Locals.** `_0` is the *return place*, where the function's result is
  written. `_1` to `_n` are the arguments, here `_1` for `urgent`. The rest are
  user variables and compiler temporaries: `_2` is `job` (the `debug` lines map
  names to locals), `_3` holds the condition, `_4` the discarded result of
  `archive`, `_5` the argument passed to it.
- **Basic blocks.** `bb0` to `bb9` are straight-line sequences of *statements*
  ending in one *terminator*, the only place where control can branch.
  `switchInt(move _3) -> [0: bb4, otherwise: bb2]` is the `if`; a call is a
  terminator too, because the callee may unwind.
- **Places.** Assignments, moves and borrows act on *places*: a local followed
  by *projections*, such as `(*_1)` (follow a reference) or `(_3 as Some).0` (a
  field of an enum variant). This is where Rust tracks moves per place rather
  than per variable, as Chapter 22 anticipated.
- **Operands.** `copy _1` reads a `Copy` value, `move _2` moves a value out
  (after it, `_2` is uninitialized), `const "backup"` is a constant.
- **Storage.** `StorageLive(_2)` and `StorageDead(_2)` mark where the local's
  stack slot comes into existence and where it is freed: the lexical scope of
  the variable, from `let` to the closing brace.
- **Drops.** `drop(_2) -> bb6` is a terminator that runs the destructor of `_2`
  *if* the value is still there. At this stage the compiler does not yet know
  whether it is, and that is the question drop elaboration answers later.
- **Unwinding.** The `unwind` targets and the `cleanup` blocks are the paths
  taken if a call panics. `FakeRead` statements are markers for the borrow
  checker that do nothing at run time.

You do not need a nightly compiler to see MIR. The stable flag `--emit=mir`
writes the MIR *after* borrow checking and optimization. Running
`rustc --edition 2024 --emit=mir -o accepts.mir examples/ch29_nll_accepts.rs`
with the pinned 1.99 and keeping the same function gives:

```text
{{#include ../../code/rust/output/ch29_maybe_archive.mir.txt}}
```

Two things changed. The storage markers and cleanup blocks are gone, and a new
local `_5: bool` has appeared: a **drop flag**, the hidden boolean of Chapter 24.
It is set to `true` in `bb0`, set back to `false` in `bb2` just before `job` is
moved into `archive`, and tested in `bb3`, which runs `drop(_2)` (in `bb5`) only
if the flag is still `true`. By the end of the section on move analysis you
will be able to compute that this flag is needed.

### The miniature MIR

The crate `mini-nll` (`code/rust/crates/mini-nll`) has a miniature MIR with the
same shapes. Its locals, blocks, program points and region variables are
newtypes around indices:

```rust
{{#include ../../code/rust/crates/mini-nll/src/mir.rs:ids}}
```

A place is a local and a list of projections:

```rust
{{#include ../../code/rust/crates/mini-nll/src/mir.rs:place}}
```

Types are reduced to what the borrow checker needs: which regions they mention,
whether they are `Copy`, whether they have a destructor. A `String` or a
`Vec<i32>` is `Owned`; a reference carries its region; `Option<&'a mut String>`
is an `Adt` with an argument:

```rust
{{#include ../../code/rust/crates/mini-nll/src/mir.rs:ty}}
```

Statements and terminators are those of the real dump, minus what this
chapter does not use. A borrow `&'k p` carries its own region variable `'k`,
and a call carries one piece of its signature, `result_borrows_from`, saying
that the result borrows from an argument, as in
`fn index<'a>(&'a Vec<T>, usize) -> &'a T`:

```rust
{{#include ../../code/rust/crates/mini-nll/src/mir.rs:rvalue}}
```

```rust
{{#include ../../code/rust/crates/mini-nll/src/mir.rs:statement}}
```

The bodies in `src/programs.rs` are translated from real functions by hand,
following the MIR that rustc builds for them. A small builder keeps the
translation readable, and attaches spans to statements *by content*, so that
error messages can point into the real source file:

```rust
{{#include ../../code/rust/crates/mini-nll/src/programs.rs:maybe_archive}}
```

Printed in rustc's format by `crates/mini-nll/examples/ch29_mir.rs`, the result
is the real dump without the unwinding machinery:

```text
{{#include ../../code/rust/output/ch29_mir.txt}}
```

The crate has nine such programs: the four functions of
`examples/ch29_nll_accepts.rs` that rustc accepts and five of this chapter's
compile-fail programs. Every analysis below runs on all of them.

## Dataflow analysis

A dataflow analysis attaches a *fact* to every program point. For the move
check, the fact at a point is "the set of places that may be uninitialized
here"; for liveness, "the set of locals whose value may still be used". Three
ingredients define an analysis.

**A lattice of facts.** The facts must be ordered by "knows less, knows more",
with a least element $\bot$ ("nothing yet") and a *join* $x \sqcup y$, the
least fact that is above both (Chapter 5 met joins in Heyting algebras). For
sets of places the order is $\subseteq$, the join is $\cup$ and $\bot$ is
$\emptyset$. Joining is what happens where control-flow paths merge: a place
that *may* be uninitialized on one incoming path may be uninitialized after the
merge.

**A transfer function** $f_n$ for every node $n$ of the graph, saying how
executing $n$ changes the facts. Most transfer functions in this chapter have
the *gen/kill* form $f_n(x) = \mathit{gen}_n \cup (x \setminus
\mathit{kill}_n)$: the statement adds some facts and removes others. A move out
of `_2` *gens* "`_2` may be uninitialized"; an assignment to `_2` *kills* it.

**A direction.** In a *forward* analysis facts flow along the edges
(initialization: what happened before determines what holds now). In a
*backward* analysis they flow against them (liveness: what happens later
determines what is live now).

The facts we want satisfy, at every node $n$ of a forward analysis, the
equation

$$
\mathit{in}(n) = \mathit{entry}(n) \sqcup \bigsqcup_{m \in \mathrm{pred}(n)} f_m(\mathit{in}(m))
$$

where $\mathit{entry}(n)$ holds the boundary facts (at the start of the
function: "every local except the arguments is uninitialized") and the big join
runs over the predecessors of $n$. A backward analysis is the same with
successors in place of predecessors. In a graph with loops the equations are
recursive, so we cannot just compute them in order. We solve them by
*iteration*: start with $\bot$ everywhere, apply the equations, and repeat until
nothing changes. If the transfer functions are **monotone** (more facts in,
more facts out) and the lattice has no infinite ascending chains, the iteration
stops, and what it stops at is the *least* solution, the most precise facts
that satisfy all the equations. We will prove all of this in Lean shortly.

### A framework in Rust

rustc has a generic dataflow framework (`rustc_mir_dataflow`) in which each
analysis supplies its lattice and transfer functions. `mini-nll` has a
miniature one, in `src/dataflow.rs`:

```rust
{{#include ../../code/rust/crates/mini-nll/src/dataflow.rs:analysis}}
```

The solver keeps one state per basic block (the facts on entry, in the
direction of the analysis) and a *worklist* of blocks to process. Processing a
block pushes its state through the block's statements and joins the result into
the next blocks; any block whose state grew goes back on the worklist:

```rust
{{#include ../../code/rust/crates/mini-nll/src/dataflow.rs:solve}}
```

The `join` method returns `true` exactly when the state grew, so the worklist
only revisits blocks that can learn something new. With monotone transfer
functions and a finite lattice, a state can only grow a finite number of times,
so the loop ends.

## Move analysis

The first analysis rustc runs answers the question behind E0382: at this point,
may this place have been moved out of (or never initialized)? rustc tracks
*move paths*, places without dereferences (`_2`, `(_3 as Some).0`), since what
lies behind a reference is not owned by the function. The analysis is
`MaybeUninit`, in `src/moves.rs`:

```rust
{{#include ../../code/rust/crates/mini-nll/src/moves.rs:maybe_uninit}}
```

Read it as gen/kill: a `move` gens its place, an assignment kills its
destination, `StorageLive` and `StorageDead` gen the local (a fresh or freed
slot holds no value), and a `drop` leaves the place uninitialized. The example
`crates/mini-nll/examples/ch29_dataflow.rs` runs it on `maybe_archive`, with
two more analyses that we will need, and prints the state on entry to each
block:

```rust
{{#include ../../code/rust/crates/mini-nll/examples/ch29_dataflow.rs:run_analysis}}
```

```text
{{#include ../../code/rust/output/ch29_dataflow.txt:1:16}}
```

Follow `_2` (`job`) through the first table. Uninitialized on entry to `bb0`,
initialized by the call to `String::from`, it is absent in `bb1` and `bb2`;
moved into `_5` in `bb2`, it is back on entry to `bb3`. Block `bb5` has two
predecessors, `bb3` (where `_2` may be uninitialized) and `bb4` (where it is
not), and the join keeps it. With no loop in the graph, each block was
processed exactly once.

### The E0382 check

With the facts in hand, the check is a loop over every use of every place:

```rust
{{#include ../../code/rust/crates/mini-nll/src/moves.rs:check_moves}}
```

When a use finds its place in the maybe-uninitialized set, the error message
needs the moves responsible, so `report_uninit_use` walks *backwards* from the
use, along every path, until it meets a move of the place (or an assignment
that initializes it, which ends that path). Here is the analysis on the variant
of `maybe_archive` that uses `job` after the `if`:

```rust
{{#include ../../code/rust/compile_fail/ch29_conditional_move.rs:conditional_move}}
```

`mini-nll` reports, in the last lines of the same output:

```text
{{#include ../../code/rust/output/ch29_dataflow.txt:29:39}}
```

and the real compiler reports:

```text
{{#include ../../code/rust/compile_fail/ch29_conditional_move.stderr}}
```

Up to rustc's extra note and suggestion, the two are identical, down to the
columns of the underlines. That is no accident of formatting: the facts are the
same facts. "Borrow of moved value" because the use is `job.len()`, which
borrows `job` (in MIR, `_7 = &_2`); "value moved here" because the backward
walk found the move `_6 = move _2` in `bb2`.

The same walk explains the loop version of the error from Chapter 6, "value
moved here, in previous iteration of loop": when the backward search from a use
in a loop body comes back around the back edge to the use itself, the move it
finds is the use's own move, one iteration earlier. (The crate's tests build
exactly this case.) And a place that was never initialized on some path gives
E0381 instead, as in `calibrate` above.

### Drop elaboration and drop flags

The dual analysis, `MaybeInit`, computes the places that *may be initialized*.
Its table is the second one in the output above. Drop elaboration combines the
two at every `drop`:

```rust
{{#include ../../code/rust/crates/mini-nll/src/moves.rs:drop_style}}
```

```text
{{#include ../../code/rust/output/ch29_dataflow.txt:25:27}}
```

At the `drop(_2)` in `bb5`, `_2` is in both sets: maybe initialized (through
`bb4`) and maybe uninitialized (through `bb3`). Only a run-time flag can tell,
which is the `_5` you saw in the optimized MIR. In `record_count`, which we
meet below, the value is moved into the return place on every path before the
`drop`, so it is definitely uninitialized there and the drop is deleted: the
optimized MIR of `record_count` has no `drop` on its normal path at all.

## Liveness

The second analysis is the one non-lexical lifetimes are built on. A local is
**live** at a point if the value it holds there may be read later, along some
path. It is a backward analysis: a *use* gens the local (reading it later makes
it live now), a *definition* kills it (whatever it held before is overwritten,
so that value is dead):

```rust
{{#include ../../code/rust/crates/mini-nll/src/liveness.rs:liveness}}
```

A `drop` counts as a use: the destructor may read the value. rustc refines this
distinction (a variable that is live only because of its drop is *drop-live*,
and only the regions its destructor may actually touch are kept alive), which
matters for types with a `Drop` impl that hold references. Our programs do not
need the refinement.

On `maybe_archive` (the third table of the output, the state on *exit* from
each block, where a backward analysis starts):

```text
{{#include ../../code/rust/output/ch29_dataflow.txt:17:24}}
```

`_2` is live on exit from `bb0` through `bb4` because the `drop(_2)` in `bb5`
reads it, and `_0` is live from the moment it is assigned until the `return`.
Notice that liveness says nothing about initialization: on exit from `bb3`,
`job` has been moved, yet it is "live" because the `drop` will look at it. Each
analysis answers one question, and the borrow checker combines them.

## Dataflow, proved

The Rust solver *is* a fixpoint computation, and the claims we made about it
(it stops, the result satisfies the equations, the result is the most precise
one) are theorems. The file `code/lean/Book/Ch29/Dataflow.lean` proves them.
Chapter 28 proved things about derivations; here we prove things about an
algorithm, so this is where the contrast between "type system" and "analysis"
becomes concrete in Lean too.

A dataflow problem has nodes `ι` and facts in a type `α` that is a
join-semilattice with a least element: Mathlib's classes `SemilatticeSup` (a
partial order with `⊔`) and `OrderBot` (with `⊥`). The `inputs` of a node are
its predecessors for a forward analysis and its successors for a backward one,
so one definition serves both directions:

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:problem}}
```

Joining a list of facts is a fold, with two lemmas that say it is the least
upper bound of the list:

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:join_all}}
```

The first lemma is proved by recursion on the list, with `rcases` splitting the
membership hypothesis into "it is the head" (and then `le_sup_left` applies) or
"it is in the tail" (and then the recursive call gives `x ≤ joinAll xs`, which
`le_sup_right` lifts past the head). The second is a term: an upper bound of
the head and of the tail is an upper bound of their join (`sup_le`).

`step` computes the right-hand side of the dataflow equations at every node at
once, and `IsSolution` says that a state satisfies every constraint: the
boundary facts are included, and so is everything that flows along an edge:

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:step}}
```

The solver is the iteration, with fuel, as in Chapter 7's normalizer: Lean
insists that every function terminates, and "repeat until nothing changes" does
not obviously do so.

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:solve}}
```

The test `P.step s = s` compares two functions `ι → α`; Lean can decide it
when `ι` is finite and equality on `α` is decidable, which is the instance the
`[DecidableEq (ι → α)]` argument asks for.

The first theorem is the basic guarantee: a converged result is a fixpoint.

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:solve_fixpoint}}
```

The proof is an induction on the fuel. With zero fuel the solver returned
`none`, so the hypothesis `none = some r` is absurd and `simp` closes the goal.
With `fuel + 1`, `unfold solve` exposes the `if`, and `split` gives one goal
per branch. In the first, `cases h` identifies `r` with `s`, and the test's
hypothesis `step s = s` is the goal. In the second, the solver recursed on
`step s`, and the induction hypothesis (stated for every starting state, which
is why `intro s r` comes after `induction`) finishes.

Next, fixpoints and solutions. A state is a solution exactly when one more
round of `step` does not take it any higher:

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:solution_iff}}
```

Left to right: `step s v` is a join, so it is below `s v` if both halves are
(`sup_le`): the boundary half by the first part of the hypothesis, the list half
by `joinAll_le`, each element of the list being, by `List.mem_map`, the transfer
of some input `u`. Right to left: `entry v` is below `step s v`
(`le_sup_left`), which is below `s v`; and each input's contribution is in the
list, hence below its join, hence below `step s v` and `s v`. A fixpoint is in
particular a solution:

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:fixpoint_solution}}
```

So the solver's answer satisfies every dataflow constraint. Is it the *best*
answer? Any state with at least the right facts at every node is a solution:
"every place may be uninitialized everywhere" satisfies all the equations of the
move analysis, and it would reject every program. We want the least solution,
and for that the transfer functions must be monotone (Chapter 17 introduced
Mathlib's `Monotone`). Then `step` is monotone too:

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:step_mono}}
```

and the result of the solver is below every solution:

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:solve_least}}
```

The proof is the classic argument for least fixpoints, again by induction on
the fuel. If the current state `s` is below a solution `t`, then `step s` is
below `step t` (monotonicity), which is below `t` (`t` is a solution, so a
post-fixpoint). Starting from `⊥`, which is below everything, every iterate
stays below `t`, and so does the final answer. In the language of the borrow
checker: the solver flags a place as maybe-uninitialized only if *every*
consistent assignment of facts would flag it too.

A useful corollary compares two problems that differ only in their boundary
facts. We will need it for regions:

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:solve_mono_entry}}
```

Finally, termination. With fuel the solver may give up, so we prove that on a
finite lattice a certain amount of fuel is always enough:

```lean
{{#include ../../code/lean/Book/Ch29/Dataflow.lean:solve_isSome}}
```

`solve_isSome` says that if the `k`-th iterate is already a fixpoint, fuel
`k + 1` suffices; its induction peels one iteration off with
`Function.iterate_succ_apply`. `solve_terminates` finds such a `k`. The iterates
`⊥, step ⊥, step (step ⊥), ...` form an ascending chain
(`monotone_nat_of_le_succ` reduces this to one step at a time, proved by
induction with `step_mono`). The first `N + 1` iterates live in a set of `N`
states, so by the pigeonhole principle (Mathlib's
`Fintype.exists_ne_map_eq_of_card_lt`) two coincide, and between two equal
elements of an ascending chain the chain is flat (`le_antisymm`): the earlier
one is a fixpoint. The bound is wildly pessimistic (the real one is the number
of nodes times the height of the lattice), but it needs no computation.

### The same analyses, in Lean

`code/lean/Book/Ch29/MoveAnalysis.lean` runs these definitions on the control
flow graph of `maybe_archive`: the same seven blocks, the same six locals.
Block-level transfer functions are gen/kill functions again (composing gen/kill
functions gives a gen/kill function), and every gen/kill function is monotone:

```lean
{{#include ../../code/lean/Book/Ch29/MoveAnalysis.lean:gen_kill}}
```

```lean
{{#include ../../code/lean/Book/Ch29/MoveAnalysis.lean:maybe_uninit}}
```

`#eval` runs the solver, and the results are exactly the tables printed by the
Rust example (maybe-uninitialized, maybe-initialized, and live on exit):

```lean
{{#include ../../code/lean/Book/Ch29/MoveAnalysis.lean:eval}}
```

The drop-flag decision becomes a boolean that `decide` evaluates, and the
general theorems apply to the concrete analysis: its answer is the least
solution, and the solver terminates (this time without running it):

```lean
{{#include ../../code/lean/Book/Ch29/MoveAnalysis.lean:drop_flag}}
```

```lean
{{#include ../../code/lean/Book/Ch29/MoveAnalysis.lean:least}}
```

`simp only [maybeUninit]` unfolds the definition so that the `match` becomes
visible, and `split` produces one goal per case, each closed by `genKill_mono`
(the `<;>` combinator runs the second tactic on every goal the first produced).

## Non-lexical lifetimes

Now the borrows. In Chapter 26 a lifetime was a *region*, and Chapter 27 ordered
regions by "outlives". Non-lexical lifetimes (NLL) give the word a precise
meaning inside a function body: **a region is a set of program points**. A
reference of type `&'a T` may be used only at points that belong to `'a`, and a
loan of a place, made by a borrow expression `&'k p`, is in force at the points
of `'k`.

The regions are the unknowns of a constraint problem. Each region variable
starts empty and must satisfy two kinds of constraints:

$$
\dfrac{x \text{ is live at } P \qquad \rho \text{ occurs in the type of } x}{P \in \rho}\;\textsf{R-Live}
\qquad\qquad
\dfrac{\rho_1 : \rho_2 \qquad P \in \rho_2}{P \in \rho_1}\;\textsf{R-Outlives}
$$

Rule R-Live is the heart of NLL: a reference keeps its region alive where it
may still be used, not where it is in scope. Rule R-Outlives reads Chapter 27's
outlives relation as inclusion of point sets. The outlives constraints come
from the statements of the body, by the subtyping rules of Chapter 27:

- an assignment `x = y` where `y: &'a T` and `x: &'b T` needs `&'a T` to be a
  subtype of `&'b T`, which (references being covariant in their region) is
  `'a: 'b`;
- a borrow `x = &'k p` gives the rvalue the type `&'k T`, so it generates
  `'k: 'b` for the region `'b` of `x`; and the point of the borrow belongs to
  `'k`;
- a **reborrow** `x = &'k *r`, where `r: &'r T`, also generates `'r: 'k`: the
  original reference must stay valid as long as the reborrow (the T-Reborrow
  rule of Chapter 28, as a constraint);
- a call relates arguments to results as the callee's signature says: `index`
  returns a reference with its argument's region.

In `mini-nll` a constraint remembers where it was generated:

```rust
{{#include ../../code/rust/crates/mini-nll/src/regions.rs:constraint}}
```

The liveness constraints give each region its starting points, using the
liveness analysis (or, for the lexical checker we will compare against, the
`StorageLive`/`StorageDead` scopes):

```rust
{{#include ../../code/rust/crates/mini-nll/src/regions.rs:liveness_constraints}}
```

A *named* lifetime parameter like the `'r` of `fn get_default<'r>` is a
**universal** region: the caller chooses it, and all the function knows is that
it outlives the whole call. So it contains every point of the body, plus a
marker `end('r)` for "the part of the caller after the call". Solving is again
a fixpoint, this time over the constraint graph:

```rust
{{#include ../../code/rust/crates/mini-nll/src/regions.rs:propagate}}
```

rustc solves the same problem more cleverly (it computes the strongly connected
components of the constraint graph and propagates once over them), but the
answer is the same least solution. Note one thing the solver *ignores*: the
`location` field. NLL treats `'a: 'b` as plain set inclusion, whatever the point
where it was generated. Remember this; it is the root of problem case #3.

### rustc's regions, and ours

Here is a function that needs everything at once:

```rust
{{#include ../../code/rust/examples/ch29_nll_accepts.rs:record_count}}
```

A nightly compiler's dump of its borrow-checking stage begins with the region
values that rustc computed. Produced like the dump of `maybe_archive` above,
with `-Zdump-mir=record_count`, with the long reasons for each constraint
shortened to `Boring(..)` and `CallArgument(..)`:

```text
{{#include ../../code/rust/output/ch29_record_count.nll.mir.txt:1:32}}
```

Below the header comes the MIR; here are its first three blocks, which
`mini-nll` reproduces statement for statement (without the `unwind` edges):

```text
{{#include ../../code/rust/output/ch29_record_count.nll.mir.txt:44:63}}
```

The points are numbered as before: `bb1[3]` is `_3 = &mut _1`, `bb1[6]` is
`_5 = &_1`, `bb1[7]` the call to `len`, `bb2[1]` the call to `push`.

`'?0` and `'?1` are free regions that rustc always creates (`'?0` is
`'static`). `'?2` is the loan of `&mut _1` at `bb1[3]` (the "Borrows" section
says so), and `'?4` the region in the type of `_3`, which receives it: hence
`'?2: '?4`. `'?4` is live from `bb1[4]` to `bb2[1]`, the call to `push` that
uses `_3`. `'?3` and `'?5` are the same story for `&_1` and `_5`, and `'?6`,
`'?7` are the regions of the callees' parameters. Now our own region
inference, from `crates/mini-nll/examples/ch29_regions.rs`:

```text
{{#include ../../code/rust/output/ch29_regions.txt:1:8}}
```

The numbering differs, but the sets are the same: the loan of `&mut _1` is
`{bb1[3..=7], bb2[0..=1]}` in both, and the shared loan `{bb1[6..=7]}`. Two
passes were enough: one to propagate, one to see that nothing changes. Note how
short the shared loan's region is: born at `bb1[6]`, dead after the call to
`len`. That will matter for two-phase borrows.

### Lexical versus non-lexical

Back to `first_then_push`. Its loan of `readings` (the `&_1` passed to
`Index::index`) has, under the two rules:

```text
{{#include ../../code/rust/output/ch29_regions.txt:9:11}}
```

Under NLL the region ends inside `bb2`, where `println!` uses `first` for the
last time; the push activates its borrow at `bb3[5]`, outside it. Under the
lexical rule the region runs to `bb5[1]`, the `StorageDead` of `first` at the
closing brace, and the lexical checker reports, in the style of pre-2018
compilers:

```text
{{#include ../../code/rust/output/ch29_regions.txt:12:22}}
```

Regions as sets of points can do something intervals of source text cannot:
leave out a branch. In `branch_borrow`, `tail` borrows `log` and is used on one
branch only:

```rust
{{#include ../../code/rust/examples/ch29_nll_accepts.rs:branch_borrow}}
```

![The program points of branch_borrow. The NLL region of the loan made by `&mut log` covers the red points only; the lexical region also covers the dashed ones, where `log` is borrowed again and moved.](../images/ch29-branch-borrow.svg)

The NLL region of the loan contains the `then` branch but not the `else`
branch, because on the `else` branch `tail` is dead. The NLL RFC (RFC 2094)
called this situation "problem case #2: conditional control flow", and NLL
solves it.

`code/lean/Book/Ch29/Regions.lean` makes the point in Lean, on the program
points of the figure:

```lean
{{#include ../../code/lean/Book/Ch29/Regions.lean:points}}
```

Liveness of the three references is one more backward `Problem` over these
points (`liveIn` in the file). Region inference is one more instance too: the
nodes are the region variables, the inputs of `'a` are the regions `'b` with
`'a: 'b`, every transfer function is the identity, and the boundary facts are
the liveness constraints. Rule R-Outlives *is* the dataflow equation.

```lean
{{#include ../../code/lean/Book/Ch29/Regions.lean:regions}}
```

The regions are numbered as in `mini-nll`: `'?0` for `tail`'s type, `'?3` for
the loan `'L`. Under NLL the loan's region is `{0, 1, 2, 3}`, under the lexical
rule `{0, ..., 7}`, and `decide` checks the consequences:

```lean
{{#include ../../code/lean/Book/Ch29/Regions.lean:verdict}}
```

The last theorem of the file is general rather than computed. If every live
reference is in scope (which is how liveness and scopes relate in any program,
since a variable can only be used while it exists), every NLL region is
contained in the corresponding lexical one. The proof is `solve_mono_entry`:
the two problems have the same edges and the same transfer functions, and
differ only in their boundary facts.

```lean
{{#include ../../code/lean/Book/Ch29/Regions.lean:nll_le_lexical}}
```

Since an error needs a loan in force at a conflicting point, smaller regions
mean fewer errors: in this model, NLL never rejects a program that the lexical
checker accepts. (The crate's tests check the inclusion on all nine programs.)

## Loans and conflicts

The last stage puts regions to work. Every borrow expression in the body
creates a **loan**:

```rust
{{#include ../../code/rust/crates/mini-nll/src/borrowck.rs:loan}}
```

A loan is *in scope* at the points reachable from its creation without leaving
its region, and without passing a point that kills it (overwriting or freeing
the local the borrowed place is based on). That is a forward analysis too, the
one rustc calls `Borrows`:

```rust
{{#include ../../code/rust/crates/mini-nll/src/borrowck.rs:borrows_apply}}
```

Then every statement is decomposed into **accesses**, each a place, a depth and
a kind:

```rust
{{#include ../../code/rust/crates/mini-nll/src/borrowck.rs:access}}
```

and each access is checked against the loans in scope at its point. Two
questions decide whether there is an error. Does the access touch the borrowed
memory? Two places conflict when one is a prefix of the other, with two
refinements: different fields are disjoint, and a *shallow* access such as
overwriting a reference does not reach what the reference points to:

```rust
{{#include ../../code/rust/crates/mini-nll/src/borrowck.rs:places_conflict}}
```

And are the access and the loan compatible? This is "aliasing XOR mutation"
from Chapter 26, as a table:

| Access | Shared loan | Mutable loan | Two-phase loan, reserved |
|---|---|---|---|
| read (`copy p`, `&p`) | ok | E0503, E0502 | ok |
| reservation of a two-phase `&mut p` | ok | E0499 | E0499 |
| `&mut p`, or an activation | E0502 | E0499 | E0499 |
| assignment `p = v` | E0506 | E0506 | E0506 |
| move out of `p` | E0505 | E0505 | E0505 |
| `StorageDead(p)`, `drop(p)` | E0597 | E0597 | E0597 |

The two-phase column, reservations and activations are explained in the next
section. In code:

```rust
{{#include ../../code/rust/crates/mini-nll/src/borrowck.rs:conflict_rules}}
```

When an access conflicts with a loan, the error message explains *why* the loan
is still in force. `explain` walks forward from the error, inside the loan's
region, to the first use of a reference that may carry the loan ("borrow later
used here"); for the lexical checker it looks for the end of the scope instead;
and when the loan flows into a named region, it points at the return. Here is
`still_used`, the version of `first_then_push` with the two middle lines
swapped:

```rust
{{#include ../../code/rust/compile_fail/ch29_still_used.rs:still_used}}
```

`crates/mini-nll/examples/ch29_nll.rs` runs four checkers on all nine programs
and prints a table of error codes, then this program's error under NLL:

```rust
{{#include ../../code/rust/crates/mini-nll/examples/ch29_nll.rs:table}}
```

```text
{{#include ../../code/rust/output/ch29_nll.txt}}
```

And here is rustc:

```text
{{#include ../../code/rust/compile_fail/ch29_still_used.stderr}}
```

The two messages are identical, and the crate's tests check that for this
program and three others: our rendering must be a prefix of rustc's `.stderr`
snapshot. The same machinery finds E0506 in `assign_while_borrowed`, where the
access is an assignment (a shallow write) to a place with a loan in scope:

```rust
{{#include ../../code/rust/compile_fail/ch29_assign_while_borrowed.rs:assign_while_borrowed}}
```

```text
{{#include ../../code/rust/compile_fail/ch29_assign_while_borrowed.stderr}}
```

Read the table column by column. The *lexical* checker rejects
`first_then_push` and `branch_borrow`, which today's compiler accepts. *NLL
without two-phase borrows* fixes those, but rejects `record_count`. *NLL*, which
is what rustc 1.99 implements, agrees with the real compiler on every one of
the nine programs: it accepts the four from `ch29_nll_accepts.rs`, and reports
exactly rustc's error codes for the five compile-fail programs. The last
column, *Polonius*, differs from NLL in one place, `get_default`. The next two
sections are about the last two columns.

## Two-phase borrows

`counts.push(counts.len())` looks innocent, but desugar it. A method call
evaluates its receiver first, so it is

```rust,ignore
Vec::push(&mut counts, Vec::len(&counts))
```

with the `&mut counts` taken *before* `&counts`, while the mutable loan is in
scope. Under the rules so far that is E0502, and that is the verdict of the
"NLL, no 2PB" column. Rust accepts it because of **two-phase borrows**: a
mutable borrow that the compiler inserts is first only *reserved*, and becomes
*active* at its first use, which here is the call to `push`. While reserved it
behaves like a shared borrow: other reads, including new shared borrows, are
allowed; writes are not. At activation it is checked again, now as a mutable
borrow against every other loan in scope. In `record_count` the shared loan of
`counts` has region `{bb1[6..=7]}`, so by the time the reservation activates
at `bb2[1]` it is gone:

```text
{{#include ../../code/rust/output/ch29_two_phase.txt:1:12}}
```

(That is `crates/mini-nll/examples/ch29_two_phase.rs`. The real dump does not
show which borrows are two-phase; `mini-nll` prints a `// two-phase` comment.)

Two-phase borrows apply to borrows the compiler inserts: the auto-referenced
receiver of a method call, the implicit reborrow of a `&mut` argument, and the
mutable borrow behind an overloaded compound assignment such as `+=` on a
`String`. All three compile, and `main` (in the same example file) checks the
result:

```rust
{{#include ../../code/rust/examples/ch29_nll_accepts.rs:two_phase_more}}
```

```text
{{#include ../../code/rust/output/ch29_nll_accepts.txt:6:6}}
```

An explicit `&mut` is an ordinary mutable borrow, active at once. Writing the
desugaring of `record_count` by hand is rejected:

```rust
{{#include ../../code/rust/compile_fail/ch29_explicit_mut_borrow.rs:explicit_mut_borrow}}
```

```text
{{#include ../../code/rust/compile_fail/ch29_explicit_mut_borrow.stderr}}
```

And a reservation tolerates *reads* before the activation, not writes. If the
argument needs a mutable borrow of the receiver, the reservation conflicts with
it:

```rust
{{#include ../../code/rust/compile_fail/ch29_two_phase_limit.rs:two_phase_limit}}
```

```text
{{#include ../../code/rust/compile_fail/ch29_two_phase_limit.stderr}}
```

`mini-nll` (the last lines of `ch29_two_phase`) reproduces the error and its
three labels, including rustc's layout of several labels on one line:

```text
{{#include ../../code/rust/output/ch29_two_phase.txt:13:21}}
```

"First borrow later used by call" points at `push`: the first loan is still
reserved, but its activation (the call) comes after the second borrow, so its
region contains the second borrow's point. rustc suggests the fix in the part of
the message we do not reproduce: evaluate `stack.pop().unwrap()` into a local
first.

## Problem case #3

The NLL RFC listed several "problem cases" that the lexical checker got wrong.
NLL solved most of them. Number 3, "conditional control flow across
functions", it did not:

```rust
{{#include ../../code/rust/compile_fail/ch29_problem_case_3.rs:problem_case_3}}
```

The function looks a key up in a cache and returns a mutable reference to the
value, inserting a default first if the key is missing. It is perfectly safe:
on the `None` path the first borrow of `cache` returned nothing, so nobody can
use it. The pinned compiler rejects it twice:

```text
{{#include ../../code/rust/compile_fail/ch29_problem_case_3.stderr}}
```

Follow the constraints. The first `get_mut` reborrows `*cache` (loan L0) and
returns `Option<&'?1 mut String>`, tied to L0's region by the signature. On the
`Some` path the reference flows into `value` and then into the return place,
whose type is `&'r mut String`; that generates `'?4: 'r` and, down the chain,
`L0: 'r`. But `'r` is a universal region: it contains every point of the body.
NLL's constraints are location-insensitive, so L0's region must contain every
point too, *including those on the `None` path*, where the second and third
mutable borrows of `*cache` happen. `crates/mini-nll/examples/ch29_polonius.rs`
shows it:

```text
{{#include ../../code/rust/output/ch29_polonius.txt:1:15}}
```

(rustc draws the "returning this value" label under the whole `match`;
`mini-nll` puts it on the returned `value`. The rest of the message is the
same, and so is the second error, which our table reports as the second
E0499.)

The problem is not the constraint `L0: 'r`. On the `Some` path it is right: the
caller receives L0's reference and may use it for all of `'r`. The problem is
that NLL has one region per loan for the whole function, so a fact that holds
on one path leaks to the other.

![The control-flow graph of get_default, simplified. Under NLL the loan L0 is in scope in every block; under Polonius it is live only in the red blocks, because on the None path no live origin contains it.](../images/ch29-problem-case-3.svg)

Until the borrow checker learns better, the workarounds trade a little
efficiency for a borrow the checker can follow: look the key up twice, or let
the standard library's entry API do the case analysis behind a single borrow:

```rust
{{#include ../../code/rust/examples/ch29_nll_accepts.rs:workarounds}}
```

```text
{{#include ../../code/rust/output/ch29_nll_accepts.txt:7:7}}
```

## Polonius

Polonius is a reformulation of the borrow checker that Niko Matsakis proposed
in 2018 as a set of Datalog rules (Datalog is a logic-programming language of
facts and rules over relations, whose meaning is a least fixpoint, like our
dataflow solver's). Its key move is to turn regions around.
In NLL a region is a set of *points*, and you ask whether a point is in a loan's
region. In Polonius a region, called an **origin**, is a set of *loans*: the
loans that a reference with that origin in its type might have come from. The
outlives constraint flips meaning accordingly. `'a: 'b` in NLL says "`'a`
contains every point of `'b`"; in Polonius it says "every loan in `'a` is also
in `'b`", written `subset('a, 'b)`. Both say that a reference may flow from
`'a` to `'b`.

The other move is to make every fact *located*: an origin contains a loan *at a
point*, and a subset relation holds *at a point*. Here are the core rules, a
simplified version of the "naive" variant of Polonius:

```text
origin_contains_loan_on_entry(O, L, P) :- loan_issued_at(O, L, P).
origin_contains_loan_on_entry(O2, L, P) :-
    origin_contains_loan_on_entry(O1, L, P), subset(O1, O2, P).
origin_contains_loan_on_entry(O, L, Q) :-
    origin_contains_loan_on_entry(O, L, P), !loan_killed_at(L, P),
    cfg_edge(P, Q), origin_live_on_entry(O, Q).

subset(O1, O2, P) :- subset_base(O1, O2, P).
subset(O1, O3, P) :- subset(O1, O2, P), subset(O2, O3, P).
subset(O1, O2, Q) :-
    subset(O1, O2, P), cfg_edge(P, Q),
    origin_live_on_entry(O1, Q), origin_live_on_entry(O2, Q).

loan_live_at(L, P) :-
    origin_contains_loan_on_entry(O, L, P), origin_live_on_entry(O, P).
errors(L, P) :- loan_invalidated_at(L, P), loan_live_at(L, P).
```

Each rule is an inference rule written sideways: the conclusion before `:-`,
the premises after it. The *input* relations come from the MIR: `cfg_edge` is
the graph, `loan_issued_at(O, L, P)` says that the borrow at `P` creates loan
`L` with origin `O`, `subset_base(O1, O2, P)` is an outlives constraint
generated at `P`, `loan_killed_at` is our kill rule, `origin_live_on_entry`
comes from liveness (a named origin like `'r` is live everywhere), and
`loan_invalidated_at` is the conflict table. Rule by rule: a loan is in its
origin where it is issued; loans flow along subset relations; facts cross a CFG
edge only into points where the origin is still live; subset relations are
transitive and survive an edge only while both origins are live. A loan is live
where a live origin contains it, and an error is an invalidated live loan.

The difference from NLL is in the edge rules. When an origin dies, its loans
are no longer carried forward, *on that path*. In `mini-nll` the rules run as
one more forward analysis of our framework, whose state at a point is the pair
of relations:

```rust
{{#include ../../code/rust/crates/mini-nll/src/polonius.rs:state}}
```

```rust
{{#include ../../code/rust/crates/mini-nll/src/polonius.rs:transfer}}
```

Filtering by liveness *on entry* to a point is the edge rule: since the join of
two states is a union, filtering after the join is the same as filtering on
each incoming edge. On `get_default`, the second half of the
`ch29_polonius` output lists, on entry to each block, the live origins that
contain L0:

```text
{{#include ../../code/rust/output/ch29_polonius.txt:16:32}}
```

`'?1` is the origin inside the type of `_3`, the `Option` returned by the first
`get_mut`, and `'?4` the origin of `value`. L0 reaches `'?1` at the call. On the
`Some` path, `_3` is still live (its payload is about to be moved out), and the
loan flows from `'?1` to `'?4` and then into `'r` at `_0 = move _7`. On the
`None` path, `_3` is dead from the first point of `bb3`, so its origin's facts
are dropped, and `'r` never received L0 on that path. No live origin contains
L0 in `bb3` to `bb8`, the borrows of `*cache` there invalidate nothing live, and
there are no errors.

### The status of Polonius

Polonius' history is a good example of why this book asks you to check the
status of ongoing work yourself. The original implementation was a separate
library, also called `polonius`, driven by a small Datalog engine, which a
nightly compiler could use instead of NLL with the unstable flag `-Zpolonius`.
It established that the formulation accepts problem case #3, but it was never
fast enough to replace NLL, and the Rust project's later work has aimed at
bringing the same location-sensitive reasoning into rustc's own analyses.

Here is what the compilers installed while this chapter was written do with
`compile_fail/ch29_problem_case_3.rs`:

- the pinned stable compiler, **rustc 1.99.0** (2026-09-28), rejects it with the
  two E0499 errors shown above;
- **rustc 1.101.0-nightly** (2026-10-08) accepts it without any flag, and rejects
  it again with the two E0499 errors when given `-Zpolonius=off`; its
  `-Zpolonius` flag accepts the values `legacy`, `off` and `next`.

So on that nightly the default borrow checker already accepts problem case #3.
Whether this has reached a stable release by the time you read this, and under
which name, is exactly the kind of thing to check rather than to remember: run
`rustc --edition 2024 --crate-type lib compile_fail/ch29_problem_case_3.rs` with
your own compiler, and look at the Rust project's announcements.

## Putting it together: `branch_borrow`, end to end

Let us take one program through the whole borrow checker, with the output of
`crates/mini-nll/examples/ch29_walkthrough.rs`, and see each stage do its job.
The program is `branch_borrow`, whose points you saw in the figure above.

**MIR and loans.** Building MIR makes every borrow explicit. There are three:
`tail = &mut log`, the two-phase reborrow `&mut *tail` for `tail.push(1)`, and
the two-phase borrow of `log` for `log.push(2)`.

```text
{{#include ../../code/rust/output/ch29_walkthrough.txt:1:3}}
```

**Move analysis.** `log` is initialized in `bb0` and only moved at the very end,
into the return place; every use finds it initialized, so the move check is
silent. (The `drop(_2)` after the move is dead, and drop elaboration will delete
it.)

**Liveness.** `tail` is assigned at `bb1[2]` and used for the last time at
`bb2[2]`, in the `then` branch. On the `else` branch it is never used, so it is
not live there:

```text
{{#include ../../code/rust/output/ch29_walkthrough.txt:4:4}}
```

**Constraints.** The assignment `tail = &'?3 mut log` gives `'?3: '?0`; the
reborrow for `tail.push(1)` gives `'?4: '?1` for its temporary and, because it
reborrows `*tail`, `'?0: '?4`; the `else` borrow gives `'?5: '?2`:

```text
{{#include ../../code/rust/output/ch29_walkthrough.txt:5:8}}
```

**Regions and loans in scope.** The point to check is `bb4[2]`, where the `else`
branch borrows `log`. The loans in scope there decide everything:

```text
{{#include ../../code/rust/output/ch29_walkthrough.txt:9:17}}
```

Under NLL, L0's region is `tail`'s liveness plus the reborrow, entirely inside
`bb1` and `bb2`; at `bb4[2]` no loan is in scope, and the program is accepted.
Under the lexical rule, L0's region is `tail`'s scope, which runs to its
`StorageDead` in `bb6`, so L0 is in scope at `bb4[2]` and again at the final
move of `log`:

```text
{{#include ../../code/rust/output/ch29_walkthrough.txt:18:}}
```

**And in Lean.** `Regions.lean` computed the same two regions on the
simplified points of the figure (`{0, 1, 2, 3}` against `{0, ..., 7}`), proved
with `decide` that the second `push` and the final move fall inside the lexical
region and outside the NLL one, and proved once and for all that NLL regions
are contained in lexical ones.

Every stage was a fixpoint over a graph; none built a derivation. The rules
enforced are those of Chapters 26 and 28 (moves are affine, `&mut` is unique, a
loan forbids conflicting accesses while it lasts), but *how long a loan lasts*
is computed from the graph, point by point.

## Common confusions

**"A lifetime is a scope."** In a function body, a lifetime is a set of program
points, computed from where references are used, and it need not be contiguous
in the source (`branch_borrow`'s loan skips the `else` branch). A lifetime
*parameter* such as `'a` in a signature is different again: a universal region
chosen by the caller, which from inside the body contains every point.

**"With NLL, a borrow ends at the last use of the variable."** Almost. A loan
lasts while *any* reference derived from it may be used: a copy of the
reference, a reborrow, a value returned to the caller, a struct holding it. And
a drop is a use: a value whose type has a destructor and holds a reference
keeps the borrow alive until the end of its scope, because the destructor runs
there.

**"The borrow checker runs on my source code."** It runs on MIR, after
desugaring: that is why a message can say "first borrow later used by call" at
a method name, the call being a terminator and the autoref a separate borrow.

**"Two-phase borrows make `&mut` a little bit shared."** Only between the
reservation and the activation, only for borrows the compiler inserts, and
only against reads. `v.push(v.pop().unwrap())` is still an error, and so is
`Vec::push(&mut v, v.len())`.

**"Rejected by the borrow checker means unsafe."** It means the analysis could
not prove the program safe. Problem case #3 is safe; NLL's facts are just not
located precisely enough. Every analysis of this kind is conservative
somewhere.

**"Polonius is a new language feature."** It changes no syntax and no typing
rule. It is a more precise analysis, designed to accept more of the programs
that are already safe.

## Summary

- rustc's borrow checker is a static analysis on MIR, not a search for
  derivations. It is flow-sensitive and conservative: it considers every path,
  without evaluating conditions.
- MIR is a control-flow graph of basic blocks whose statements act on places;
  `StorageLive`/`StorageDead` mark scopes, `drop` runs destructors, and drop
  elaboration adds drop flags where needed. `--emit=mir` shows MIR on stable,
  `-Zdump-mir` every stage on nightly.
- A dataflow analysis is a lattice of facts, monotone transfer functions and a
  direction; the worklist algorithm finds the least solution. In Lean we proved
  that a converged result is a fixpoint, that it satisfies every constraint,
  that it is the least solution, and that enough fuel always exists.
- Maybe-uninitialized places give E0382 and E0381; maybe-initialized places
  together with them decide drop flags; liveness is backward and feeds
  regions.
- NLL regions are sets of points: liveness constraints plus outlives
  constraints, solved by propagation. Loans are in scope where their region
  allows, and an access that conflicts with a loan in scope is E0499, E0502,
  E0503, E0505, E0506 or E0597. NLL regions are contained in lexical ones.
- Two-phase borrows reserve compiler-inserted mutable borrows and activate them
  at first use, which accepts `v.push(v.len())`.
- NLL's constraints are location-insensitive, which rejects problem case #3.
  Polonius makes origins sets of loans and locates every fact on the graph, and
  accepts it. rustc 1.99 rejects it; the nightly of October 2026 accepts it.

## Exercises

1. Hand-run the move analysis on this loop, block by block, and explain the
   error rustc gives ("value moved here, in previous iteration of loop"):
   `fn send_all(msg: String) { loop { consume(msg); } }`. How many times does
   the worklist process the loop block before the fixpoint?
   *Hint:* the MIR has `bb0: goto -> bb1` and
   `bb1: _2 = consume(move _1) -> bb1`. On the first visit `_1` is initialized
   on entry to `bb1`; the back edge joins in the state after the move.

2. Add a program to `mini-nll`: translate
   `fn shrink(v: &mut Vec<i32>) { let first = &v[0]; v.clear(); println!("{first}"); }`
   to the miniature MIR, check that the NLL checker reports E0502, and compare
   its message with rustc's.
   *Hint:* copy `still_used`; the borrowed place is now `*v`, so use
   `deref(v)` for the borrow, and give `v` a type with a region of its own.

3. In Lean, define a *must* analysis ("definitely initialized") on the
   `maybe_archive` graph. Its merge operation is intersection and it starts
   from "everything", so it does not fit `Problem` as it stands: write a small
   solver of your own that starts every block at `Finset.univ` and intersects
   at merge points, then prove with `decide` that on every block its answer is
   the complement of `maybeUninit`'s.
   *Hint:* a place is definitely initialized exactly when it is not maybe
   uninitialized; `Finset.univ \ s` is the complement of `s`.

4. In Lean, prove that `step` is *inflationary* on the iterates from `⊥`: for
   every `k`, `P.step^[k] ⊥ ≤ P.step^[k + 1] ⊥`, assuming monotone transfer
   functions. (The proof of `solve_terminates` contains it; extract it as a
   lemma of its own.)
   *Hint:* induction on `k`; the base case is `bot_le`, the step uses
   `Function.iterate_succ_apply'` and `step_mono`.

5. Rewrite `get_default` with a `match` on `cache.contains_key(&key)` in a way
   that NLL accepts, and explain in terms of loans and regions why your version
   is accepted while problem case #3 is not.
   *Hint:* `contains_key` takes `&self` and returns a `bool`, which carries no
   loan; after it returns, no reference derived from `cache` is live.

6. Using the Polonius rules of this chapter, compute by hand which origins
   contain the loan of `readings` at each point of `still_used`, and confirm
   that `errors` contains the activation of the push. Then do the same for
   `first_then_push` and show that `errors` is empty.
   *Hint:* the loan flows from the borrow's origin into `_3`'s, then through
   `index` into `first`'s; the only question at the push is whether `first` is
   live there.
