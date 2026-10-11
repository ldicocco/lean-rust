//! Real Rust functions, translated to the miniature MIR by hand.
//!
//! Each body follows the MIR that rustc builds for the function (as dumped
//! by `rustc -Zdump-mir=<fn>` on a nightly compiler), minus unwinding edges
//! and cleanup blocks, with library calls reduced to their signatures and
//! `println!` reduced to one borrow and one call. The source text is
//! included from the files that rustc itself checks, so that the line
//! numbers in our diagnostics match rustc's.

use crate::build::{Builder, copy, cst, deref, mv};
use crate::mir::*;

const ACCEPTS: &str = include_str!("../../../examples/ch29_nll_accepts.rs");
const ACCEPTS_FILE: &str = "examples/ch29_nll_accepts.rs";

use BorrowKind::{Mut, Shared, TwoPhaseMut};

/// The programs, in the order the chapter discusses them.
pub fn all() -> Vec<Body> {
    vec![
        maybe_archive(),
        conditional_move(),
        first_then_push(),
        still_used(),
        branch_borrow(),
        assign_while_borrowed(),
        record_count(),
        rotate_top(),
        problem_case_3(),
    ]
}

pub fn by_name(name: &str) -> Body {
    all()
        .into_iter()
        .find(|b| b.name == name)
        .unwrap_or_else(|| panic!("no program `{name}`"))
}

// ANCHOR: maybe_archive
/// ```text
/// fn maybe_archive(urgent: bool) {
///     let job = String::from("backup");
///     if urgent {
///         archive(job);
///     }
/// }
/// ```
pub fn maybe_archive() -> Body {
    let mut b = Builder::new("maybe_archive", ACCEPTS_FILE, ACCEPTS);
    b.ret(scalar("()"));
    let urgent = b.arg(
        "urgent",
        scalar("bool"),
        b.span("fn maybe_archive", "urgent"),
    );
    let job = b.var("job", owned("String"), b.span("let job", "job"));
    let cond = b.temp(scalar("bool"));
    let archived = b.temp(scalar("usize"));
    let arg = b.temp(owned("String"));
    let [bb0, bb1, bb2, bb3, bb4, bb5, bb6] = [(); 7].map(|_| b.block());

    b.storage_live(bb0, job);
    let from = b.span("let job", "String::from(\"backup\")");
    let callee = b.span("let job", "String::from");
    b.call(bb0, job, "String::from", vec![cst("\"backup\"")], bb1)
        .spans(from, callee);

    b.fake_read(bb1, job);
    b.storage_live(bb1, cond);
    b.assign(bb1, cond, Rvalue::Use(copy(urgent)), None);
    b.switch(bb1, mv(cond), vec![("0", bb4), ("otherwise", bb2)]);

    b.storage_live(bb2, archived);
    b.storage_live(bb2, arg);
    let moved = b.span("archive(job)", "job");
    b.assign(bb2, arg, Rvalue::Use(mv(job)), Some(moved));
    let call = b.span("archive(job)", "archive(job)");
    let callee = b.span("archive(job)", "archive");
    b.call(bb2, archived, "archive", vec![mv(arg)], bb3)
        .spans(call, callee);

    b.storage_dead(bb3, arg);
    b.storage_dead(bb3, archived);
    b.assign(bb3, Local(0), Rvalue::Use(cst("()")), None);
    b.goto(bb3, bb5);

    b.assign(bb4, Local(0), Rvalue::Use(cst("()")), None);
    b.goto(bb4, bb5);

    b.storage_dead(bb5, cond);
    b.drop(bb5, job, bb6);

    let end = b.closing_brace();
    b.storage_dead_at(bb6, job, end);
    b.ret_term(bb6);
    b.finish()
}
// ANCHOR_END: maybe_archive

/// `maybe_archive` plus a use of `job` after the `if`: E0382.
pub fn conditional_move() -> Body {
    let source = include_str!("../../../compile_fail/ch29_conditional_move.rs");
    let mut b = Builder::new(
        "conditional_move",
        "compile_fail/ch29_conditional_move.rs",
        source,
    );
    b.ret(scalar("usize"));
    let urgent = b.arg(
        "urgent",
        scalar("bool"),
        b.span("fn conditional_move", "urgent"),
    );
    let job = b.var("job", owned("String"), b.span("let job", "job"));
    let unit = b.temp(scalar("()"));
    let cond = b.temp(scalar("bool"));
    let archived = b.temp(scalar("usize"));
    let arg = b.temp(owned("String"));
    let job_ref = b.shared(owned("String"));
    let job_ref = b.temp(job_ref);
    let [bb0, bb1, bb2, bb3, bb4, bb5, bb6, bb7] = [(); 8].map(|_| b.block());

    b.storage_live(bb0, job);
    let from = b.span("let job", "String::from(\"backup\")");
    let callee = b.span("let job", "String::from");
    b.call(bb0, job, "String::from", vec![cst("\"backup\"")], bb1)
        .spans(from, callee);

    b.fake_read(bb1, job);
    b.storage_live(bb1, unit);
    b.storage_live(bb1, cond);
    b.assign(bb1, cond, Rvalue::Use(copy(urgent)), None);
    b.switch(bb1, mv(cond), vec![("0", bb4), ("otherwise", bb2)]);

    b.storage_live(bb2, archived);
    b.storage_live(bb2, arg);
    let moved = b.span("archive(job)", "job");
    b.assign(bb2, arg, Rvalue::Use(mv(job)), Some(moved));
    let call = b.span("archive(job)", "archive(job)");
    let callee = b.span("archive(job)", "archive");
    b.call(bb2, archived, "archive", vec![mv(arg)], bb3)
        .spans(call, callee);

    b.storage_dead(bb3, arg);
    b.storage_dead(bb3, archived);
    b.assign(bb3, unit, Rvalue::Use(cst("()")), None);
    b.goto(bb3, bb5);

    b.assign(bb4, unit, Rvalue::Use(cst("()")), None);
    b.goto(bb4, bb5);

    b.storage_dead(bb5, cond);
    b.storage_dead(bb5, unit);
    b.storage_live(bb5, job_ref);
    b.borrow(bb5, job_ref, Shared, job, b.span("job.len()", "job"));
    let call = b.span("job.len()", "job.len()");
    let callee = b.span("job.len()", "len");
    b.call(bb5, Local(0), "String::len", vec![mv(job_ref)], bb6)
        .spans(call, callee);

    b.storage_dead(bb6, job_ref);
    b.drop(bb6, job, bb7);

    let end = b.closing_brace();
    b.storage_dead_at(bb7, job, end);
    b.ret_term(bb7);
    b.finish()
}

/// `let first = &readings[0];` as a borrow plus a call to `Index::index`,
/// whose signature ties the result to the borrow.
fn first_of_readings(
    b: &mut Builder,
    bb: BlockId,
    next: BlockId,
    readings: Local,
    first: Local,
) {
    let vec_ref = b.shared(owned("Vec<i32>"));
    let vec_ref = b.temp(vec_ref);
    b.storage_live(bb, first);
    b.storage_live(bb, vec_ref);
    b.borrow(
        bb,
        vec_ref,
        Shared,
        readings,
        b.span("let first", "readings"),
    );
    let call = b.span("let first", "readings[0]");
    let args = vec![mv(vec_ref), cst("0_usize")];
    b.call(bb, first, "Index::index", args, next)
        .borrows_from(0)
        .spans(call, call);
    b.storage_dead(next, vec_ref);
    b.fake_read(next, first);
}

/// `println!("first = {first}")` as a borrow of `first` and a call.
fn print_first(b: &mut Builder, bb: BlockId, next: BlockId, first: Local) {
    let unit = b.temp(scalar("()"));
    let inner = b.shared(scalar("i32"));
    let arg = b.shared(inner);
    let arg = b.temp(arg);
    b.storage_live(bb, unit);
    b.storage_live(bb, arg);
    b.borrow(bb, arg, Shared, first, b.span_nth("println!", "first", 1));
    let call = b.span("println!", "println!(\"first = {first}\")");
    let callee = b.span("println!", "println!");
    b.call(bb, unit, "_print", vec![mv(arg)], next)
        .spans(call, callee);
    b.storage_dead(next, arg);
    b.storage_dead(next, unit);
}

/// `readings.push(40)`: a two-phase borrow of the receiver, then the call.
fn push_reading(b: &mut Builder, bb: BlockId, next: BlockId, readings: Local) {
    let unit = b.temp(scalar("()"));
    let recv = b.mutable(owned("Vec<i32>"));
    let recv = b.temp(recv);
    b.storage_live(bb, unit);
    b.storage_live(bb, recv);
    b.borrow(
        bb,
        recv,
        TwoPhaseMut,
        readings,
        b.span("readings.push", "readings"),
    );
    let call = b.span("readings.push", "readings.push(40)");
    let callee = b.span("readings.push", "push");
    let args = vec![mv(recv), cst("40_i32")];
    b.call(bb, unit, "Vec::push", args, next)
        .spans(call, callee);
    b.storage_dead(next, recv);
    b.storage_dead(next, unit);
}

// ANCHOR: first_then_push
/// ```text
/// fn first_then_push() -> usize {
///     let mut readings = vec![10, 20, 30];
///     let first = &readings[0];
///     println!("first = {first}");
///     readings.push(40);
///     readings.len()
/// }
/// ```
pub fn first_then_push() -> Body {
    let mut b = Builder::new("first_then_push", ACCEPTS_FILE, ACCEPTS);
    b.ret(scalar("usize"));
    let readings = b.var(
        "readings",
        owned("Vec<i32>"),
        b.span("let mut readings", "readings"),
    );
    let first = b.shared(scalar("i32"));
    let first = b.var("first", first, b.span("let first", "first"));
    let [bb0, bb1, bb2, bb3, bb4, bb5, bb6] = [(); 7].map(|_| b.block());

    b.storage_live(bb0, readings);
    let vec = b.span("let mut readings", "vec![10, 20, 30]");
    let callee = b.span("let mut readings", "vec!");
    b.call(bb0, readings, "vec", vec![cst("[10, 20, 30]")], bb1)
        .spans(vec, callee);
    b.fake_read(bb1, readings);
    first_of_readings(&mut b, bb1, bb2, readings, first);
    print_first(&mut b, bb2, bb3, first);
    push_reading(&mut b, bb3, bb4, readings);

    let len_ref = b.shared(owned("Vec<i32>"));
    let len_ref = b.temp(len_ref);
    b.storage_live(bb4, len_ref);
    b.borrow(
        bb4,
        len_ref,
        Shared,
        readings,
        b.span("readings.len()", "readings"),
    );
    let call = b.span("readings.len()", "readings.len()");
    let callee = b.span("readings.len()", "len");
    b.call(bb4, Local(0), "Vec::len", vec![mv(len_ref)], bb5)
        .spans(call, callee);

    b.storage_dead(bb5, len_ref);
    let end = b.closing_brace();
    b.storage_dead_at(bb5, first, end);
    b.drop(bb5, readings, bb6);
    b.storage_dead_at(bb6, readings, end);
    b.ret_term(bb6);
    b.finish()
}
// ANCHOR_END: first_then_push

/// The same statements as `first_then_push`, with the push before the print.
pub fn still_used() -> Body {
    let source = include_str!("../../../compile_fail/ch29_still_used.rs");
    let mut b = Builder::new("still_used", "compile_fail/ch29_still_used.rs", source);
    b.ret(scalar("()"));
    let readings = b.var(
        "readings",
        owned("Vec<i32>"),
        b.span("let mut readings", "readings"),
    );
    let first = b.shared(scalar("i32"));
    let first = b.var("first", first, b.span("let first", "first"));
    let [bb0, bb1, bb2, bb3, bb4, bb5] = [(); 6].map(|_| b.block());

    b.storage_live(bb0, readings);
    let vec = b.span("let mut readings", "vec![10, 20, 30]");
    let callee = b.span("let mut readings", "vec!");
    b.call(bb0, readings, "vec", vec![cst("[10, 20, 30]")], bb1)
        .spans(vec, callee);
    b.fake_read(bb1, readings);
    first_of_readings(&mut b, bb1, bb2, readings, first);
    push_reading(&mut b, bb2, bb3, readings);
    print_first(&mut b, bb3, bb4, first);

    b.assign(bb4, Local(0), Rvalue::Use(cst("()")), None);
    let end = b.closing_brace();
    b.storage_dead_at(bb4, first, end);
    b.drop(bb4, readings, bb5);
    b.storage_dead_at(bb5, readings, end);
    b.ret_term(bb5);
    b.finish()
}

// ANCHOR: branch_borrow
/// ```text
/// fn branch_borrow(verbose: bool) -> Vec<u32> {
///     let mut log = Vec::new();
///     let tail = &mut log;
///     if verbose {
///         tail.push(1);
///     } else {
///         log.push(2);
///     }
///     log
/// }
/// ```
pub fn branch_borrow() -> Body {
    let mut b = Builder::new("branch_borrow", ACCEPTS_FILE, ACCEPTS);
    b.ret(owned("Vec<u32>"));
    let verbose = b.arg(
        "verbose",
        scalar("bool"),
        b.span("fn branch_borrow", "verbose"),
    );
    let log = b.var("log", owned("Vec<u32>"), b.span("let mut log", "log"));
    let tail = b.mutable(owned("Vec<u32>"));
    let tail = b.var("tail", tail, b.span("let tail", "tail"));
    let unit = b.temp(scalar("()"));
    let cond = b.temp(scalar("bool"));
    let then_unit = b.temp(scalar("()"));
    let then_recv = b.mutable(owned("Vec<u32>"));
    let then_recv = b.temp(then_recv);
    let else_unit = b.temp(scalar("()"));
    let else_recv = b.mutable(owned("Vec<u32>"));
    let else_recv = b.temp(else_recv);
    let [bb0, bb1, bb2, bb3, bb4, bb5, bb6, bb7] = [(); 8].map(|_| b.block());

    b.storage_live(bb0, log);
    let new = b.span("let mut log", "Vec::new()");
    b.call(bb0, log, "Vec::new", vec![], bb1).spans(new, new);

    b.fake_read(bb1, log);
    b.storage_live(bb1, tail);
    b.borrow(bb1, tail, Mut, log, b.span("let tail", "&mut log"));
    b.fake_read(bb1, tail);
    b.storage_live(bb1, unit);
    b.storage_live(bb1, cond);
    b.assign(bb1, cond, Rvalue::Use(copy(verbose)), None);
    b.switch(bb1, mv(cond), vec![("0", bb4), ("otherwise", bb2)]);

    // then: tail.push(1), a two-phase reborrow of `*tail`
    b.storage_live(bb2, then_unit);
    b.storage_live(bb2, then_recv);
    b.borrow(
        bb2,
        then_recv,
        TwoPhaseMut,
        deref(tail),
        b.span("tail.push", "tail"),
    );
    let call = b.span("tail.push", "tail.push(1)");
    let callee = b.span("tail.push", "push");
    let args = vec![mv(then_recv), cst("1_u32")];
    b.call(bb2, then_unit, "Vec::push", args, bb3)
        .spans(call, callee);
    b.storage_dead(bb3, then_recv);
    b.storage_dead(bb3, then_unit);
    b.assign(bb3, unit, Rvalue::Use(cst("()")), None);
    b.goto(bb3, bb6);

    // else: log.push(2)
    b.storage_live(bb4, else_unit);
    b.storage_live(bb4, else_recv);
    b.borrow(bb4, else_recv, TwoPhaseMut, log, b.span("log.push", "log"));
    let call = b.span("log.push", "log.push(2)");
    let callee = b.span("log.push", "push");
    let args = vec![mv(else_recv), cst("2_u32")];
    b.call(bb4, else_unit, "Vec::push", args, bb5)
        .spans(call, callee);
    b.storage_dead(bb5, else_recv);
    b.storage_dead(bb5, else_unit);
    b.assign(bb5, unit, Rvalue::Use(cst("()")), None);
    b.goto(bb5, bb6);

    b.storage_dead(bb6, cond);
    b.storage_dead(bb6, unit);
    b.assign(
        bb6,
        Local(0),
        Rvalue::Use(mv(log)),
        Some(b.span_exact("    log")),
    );
    let end = b.closing_brace();
    b.storage_dead_at(bb6, tail, end);
    b.drop(bb6, log, bb7);
    b.storage_dead_at(bb7, log, end);
    b.ret_term(bb7);
    b.finish()
}
// ANCHOR_END: branch_borrow

/// ```text
/// fn assign_while_borrowed() -> i32 {
///     let mut total = 10;
///     let r = &total;
///     total = 20;
///     *r + total
/// }
/// ```
pub fn assign_while_borrowed() -> Body {
    let source = include_str!("../../../compile_fail/ch29_assign_while_borrowed.rs");
    let file = "compile_fail/ch29_assign_while_borrowed.rs";
    let mut b = Builder::new("assign_while_borrowed", file, source);
    b.ret(scalar("i32"));
    let total = b.var("total", scalar("i32"), b.span("let mut total", "total"));
    let r = b.shared(scalar("i32"));
    let r = b.var("r", r, b.span("let r", "r"));
    let lhs = b.temp(scalar("i32"));
    let rhs = b.temp(scalar("i32"));
    let bb0 = b.block();

    b.storage_live(bb0, total);
    let init = b.span("let mut total", "10");
    b.assign(bb0, total, Rvalue::Use(cst("10_i32")), Some(init));
    b.fake_read(bb0, total);
    b.storage_live(bb0, r);
    b.borrow(bb0, r, Shared, total, b.span("let r", "&total"));
    b.fake_read(bb0, r);
    let assign = b.span("total = 20", "total = 20");
    b.assign(bb0, total, Rvalue::Use(cst("20_i32")), Some(assign));
    b.storage_live(bb0, lhs);
    b.assign(
        bb0,
        lhs,
        Rvalue::Use(copy(deref(r))),
        Some(b.span("*r + total", "*r")),
    );
    b.storage_live(bb0, rhs);
    let rhs_span = b.span("*r + total", "total");
    b.assign(bb0, rhs, Rvalue::Use(copy(total)), Some(rhs_span));
    let sum = Rvalue::BinaryOp("Add", mv(lhs), mv(rhs));
    b.assign(bb0, Local(0), sum, Some(b.span("*r + total", "*r + total")));
    b.storage_dead(bb0, rhs);
    b.storage_dead(bb0, lhs);
    let end = b.closing_brace();
    b.storage_dead_at(bb0, r, end);
    b.storage_dead_at(bb0, total, end);
    b.ret_term(bb0);
    b.finish()
}

// ANCHOR: record_count
/// ```text
/// fn record_count() -> Vec<usize> {
///     let mut counts = Vec::new();
///     counts.push(counts.len());
///     counts
/// }
/// ```
pub fn record_count() -> Body {
    let mut b = Builder::new("record_count", ACCEPTS_FILE, ACCEPTS);
    b.ret(owned("Vec<usize>"));
    let counts = b.var(
        "counts",
        owned("Vec<usize>"),
        b.span("let mut counts", "counts"),
    );
    let unit = b.temp(scalar("()"));
    let recv = b.mutable(owned("Vec<usize>"));
    let recv = b.temp(recv);
    let len = b.temp(scalar("usize"));
    let len_ref = b.shared(owned("Vec<usize>"));
    let len_ref = b.temp(len_ref);
    let [bb0, bb1, bb2, bb3, bb4] = [(); 5].map(|_| b.block());

    b.storage_live(bb0, counts);
    let new = b.span("let mut counts", "Vec::new()");
    b.call(bb0, counts, "Vec::new", vec![], bb1).spans(new, new);

    b.fake_read(bb1, counts);
    b.storage_live(bb1, unit);
    b.storage_live(bb1, recv);
    let line = "counts.push(counts.len())";
    b.borrow(bb1, recv, TwoPhaseMut, counts, b.span(line, "counts"));
    b.storage_live(bb1, len);
    b.storage_live(bb1, len_ref);
    b.borrow(bb1, len_ref, Shared, counts, b.span_nth(line, "counts", 1));
    let call = b.span(line, "counts.len()");
    let callee = b.span(line, "len");
    b.call(bb1, len, "Vec::len", vec![mv(len_ref)], bb2)
        .spans(call, callee);

    b.storage_dead(bb2, len_ref);
    let call = b.span(line, line);
    let callee = b.span(line, "push");
    let args = vec![mv(recv), mv(len)];
    b.call(bb2, unit, "Vec::push", args, bb3)
        .spans(call, callee);

    b.storage_dead(bb3, len);
    b.storage_dead(bb3, recv);
    b.storage_dead(bb3, unit);
    let ret = b.span_exact("    counts");
    b.assign(bb3, Local(0), Rvalue::Use(mv(counts)), Some(ret));
    b.drop(bb3, counts, bb4);

    let end = b.closing_brace();
    b.storage_dead_at(bb4, counts, end);
    b.ret_term(bb4);
    b.finish()
}
// ANCHOR_END: record_count

/// ```text
/// fn rotate_top(stack: &mut Vec<i32>) {
///     stack.push(stack.pop().unwrap());
/// }
/// ```
pub fn rotate_top() -> Body {
    let source = include_str!("../../../compile_fail/ch29_two_phase_limit.rs");
    let file = "compile_fail/ch29_two_phase_limit.rs";
    let mut b = Builder::new("rotate_top", file, source);
    b.ret(scalar("()"));
    let stack = b.mutable(owned("Vec<i32>"));
    let stack = b.arg("stack", stack, b.span("fn rotate_top", "stack"));
    let unit = b.temp(scalar("()"));
    let recv = b.mutable(owned("Vec<i32>"));
    let recv = b.temp(recv);
    let top = b.temp(scalar("i32"));
    let popped = b.temp(adt("Option", vec![scalar("i32")]));
    let pop_recv = b.mutable(owned("Vec<i32>"));
    let pop_recv = b.temp(pop_recv);
    let [bb0, bb1, bb2, bb3] = [(); 4].map(|_| b.block());

    let line = "stack.push(stack.pop().unwrap())";
    b.storage_live(bb0, unit);
    b.storage_live(bb0, recv);
    b.borrow(bb0, recv, TwoPhaseMut, deref(stack), b.span(line, "stack"));
    b.storage_live(bb0, top);
    b.storage_live(bb0, popped);
    b.storage_live(bb0, pop_recv);
    b.borrow(
        bb0,
        pop_recv,
        TwoPhaseMut,
        deref(stack),
        b.span_nth(line, "stack", 1),
    );
    let call = b.span(line, "stack.pop()");
    let callee = b.span(line, "pop");
    b.call(bb0, popped, "Vec::pop", vec![mv(pop_recv)], bb1)
        .spans(call, callee);

    b.storage_dead(bb1, pop_recv);
    let call = b.span(line, "stack.pop().unwrap()");
    let callee = b.span(line, "unwrap");
    b.call(bb1, top, "Option::unwrap", vec![mv(popped)], bb2)
        .spans(call, callee);

    b.storage_dead(bb2, popped);
    let call = b.span(line, line);
    let callee = b.span(line, "push");
    b.call(bb2, unit, "Vec::push", vec![mv(recv), mv(top)], bb3)
        .spans(call, callee);

    b.storage_dead(bb3, top);
    b.storage_dead(bb3, recv);
    b.storage_dead(bb3, unit);
    b.assign(bb3, Local(0), Rvalue::Use(cst("()")), None);
    b.ret_term(bb3);
    b.finish()
}

// ANCHOR: problem_case_3
/// ```text
/// fn get_default<'r>(cache: &'r mut HashMap<u32, String>, key: u32) -> &'r mut String {
///     match cache.get_mut(&key) {
///         Some(value) => value,
///         None => {
///             cache.insert(key, String::new());
///             cache.get_mut(&key).unwrap()
///         }
///     }
/// }
/// ```
pub fn problem_case_3() -> Body {
    let source = include_str!("../../../compile_fail/ch29_problem_case_3.rs");
    let file = "compile_fail/ch29_problem_case_3.rs";
    let mut b = Builder::new("get_default", file, source);
    let map = || owned("HashMap<u32, String>");
    let r = b.universal("'r", b.span("fn get_default", "'r"));
    b.ret(Ty::Ref(r, Mutability::Mut, Box::new(owned("String"))));
    let cache_ty = Ty::Ref(r, Mutability::Mut, Box::new(map()));
    let cache = b.arg("cache", cache_ty, b.span("fn get_default", "cache"));
    let key = b.arg("key", scalar("u32"), b.span("fn get_default", "key"));
    let found_ref = b.mutable(owned("String"));
    let found = b.temp(adt("Option", vec![found_ref]));
    let recv = b.mutable(map());
    let recv = b.temp(recv);
    let key_ref = b.shared(scalar("u32"));
    let key_ref = b.temp(key_ref);
    let discr = b.temp(scalar("isize"));
    let value = b.mutable(owned("String"));
    let value = b.var("value", value, b.span("Some(value)", "value"));
    let old = b.temp(adt("Option", vec![owned("String")]));
    let ins_recv = b.mutable(map());
    let ins_recv = b.temp(ins_recv);
    let empty = b.temp(owned("String"));
    let again_ref = b.mutable(owned("String"));
    let again = b.temp(adt("Option", vec![again_ref]));
    let again_recv = b.mutable(map());
    let again_recv = b.temp(again_recv);
    let again_key = b.shared(scalar("u32"));
    let again_key = b.temp(again_key);
    let [bb0, bb1, bb2, bb3, bb4, bb5, bb6, bb7, bb8, bb9] =
        [(); 10].map(|_| b.block());

    // match cache.get_mut(&key) {
    let line = "match cache.get_mut(&key)";
    b.storage_live(bb0, found);
    b.storage_live(bb0, recv);
    b.borrow(bb0, recv, TwoPhaseMut, deref(cache), b.span(line, "cache"));
    b.storage_live(bb0, key_ref);
    b.borrow(bb0, key_ref, Shared, key, b.span(line, "&key"));
    let call = b.span(line, "cache.get_mut(&key)");
    let callee = b.span(line, "get_mut");
    let args = vec![mv(recv), mv(key_ref)];
    b.call(bb0, found, "HashMap::get_mut", args, bb1)
        .borrows_from(0)
        .spans(call, callee);

    b.storage_dead(bb1, key_ref);
    b.storage_dead(bb1, recv);
    b.assign(bb1, discr, Rvalue::Discriminant(found.into()), None);
    b.switch(bb1, mv(discr), vec![("0", bb3), ("1", bb2)]);

    // Some(value) => value,
    b.storage_live(bb2, value);
    let payload = Place::from(found).downcast("Some").field(0);
    b.assign(bb2, value, Rvalue::Use(mv(payload)), None);
    let returned = b.span_nth("Some(value)", "value", 1);
    b.assign(bb2, Local(0), Rvalue::Use(mv(value)), Some(returned));
    b.storage_dead(bb2, value);
    b.goto(bb2, bb9);

    // None => { cache.insert(key, String::new());
    let line = "cache.insert(key, String::new())";
    b.storage_live(bb3, old);
    b.storage_live(bb3, ins_recv);
    b.borrow(
        bb3,
        ins_recv,
        TwoPhaseMut,
        deref(cache),
        b.span(line, "cache"),
    );
    b.storage_live(bb3, empty);
    let call = b.span(line, "String::new()");
    b.call(bb3, empty, "String::new", vec![], bb4)
        .spans(call, call);

    let call = b.span(line, line);
    let callee = b.span(line, "insert");
    let args = vec![mv(ins_recv), copy(key), mv(empty)];
    b.call(bb4, old, "HashMap::insert", args, bb5)
        .spans(call, callee);

    b.storage_dead(bb5, empty);
    b.storage_dead(bb5, ins_recv);
    b.drop(bb5, old, bb6);

    // cache.get_mut(&key).unwrap()
    let line = "cache.get_mut(&key).unwrap()";
    b.storage_dead(bb6, old);
    b.storage_live(bb6, again);
    b.storage_live(bb6, again_recv);
    b.borrow(
        bb6,
        again_recv,
        TwoPhaseMut,
        deref(cache),
        b.span(line, "cache"),
    );
    b.storage_live(bb6, again_key);
    b.borrow(bb6, again_key, Shared, key, b.span(line, "&key"));
    let call = b.span(line, "cache.get_mut(&key)");
    let callee = b.span(line, "get_mut");
    let args = vec![mv(again_recv), mv(again_key)];
    b.call(bb6, again, "HashMap::get_mut", args, bb7)
        .borrows_from(0)
        .spans(call, callee);

    b.storage_dead(bb7, again_key);
    b.storage_dead(bb7, again_recv);
    let call = b.span(line, line);
    let callee = b.span(line, "unwrap");
    b.call(bb7, Local(0), "Option::unwrap", vec![mv(again)], bb8)
        .borrows_from(0)
        .spans(call, callee);

    b.storage_dead(bb8, again);
    b.goto(bb8, bb9);

    b.storage_dead(bb9, found);
    b.ret_term(bb9);
    b.finish()
}
// ANCHOR_END: problem_case_3

#[cfg(test)]
mod tests {
    use super::*;
    use crate::borrowck::{Checker, check, collect_loans};
    use crate::moves::{DropStyle, drop_styles};
    use crate::regions::{RegionMode, describe_points, infer};

    fn codes(body: &Body, checker: Checker) -> Vec<&'static str> {
        check(body, checker).iter().map(|d| d.code).collect()
    }

    /// What rustc 1.99 reports for the real functions.
    const RUSTC: [(&str, &[&str]); 9] = [
        ("maybe_archive", &[]),
        ("conditional_move", &["E0382"]),
        ("first_then_push", &[]),
        ("still_used", &["E0502"]),
        ("branch_borrow", &[]),
        ("assign_while_borrowed", &["E0506"]),
        ("record_count", &[]),
        ("rotate_top", &["E0499"]),
        ("get_default", &["E0499", "E0499"]),
    ];

    #[test]
    fn nll_agrees_with_rustc() {
        for (name, expected) in RUSTC {
            assert_eq!(codes(&by_name(name), Checker::Nll), expected, "{name}");
        }
    }

    #[test]
    fn lexical_rejects_more_and_polonius_accepts_more() {
        let lexical = codes(&first_then_push(), Checker::Lexical);
        assert_eq!(lexical, ["E0502"]);
        assert_eq!(
            codes(&branch_borrow(), Checker::Lexical),
            ["E0499", "E0505"]
        );
        assert_eq!(
            codes(&record_count(), Checker::NllWithoutTwoPhase),
            ["E0502"]
        );
        assert!(codes(&problem_case_3(), Checker::Polonius).is_empty());
        // Every program NLL accepts is accepted by Polonius too.
        for body in all() {
            if codes(&body, Checker::Nll).is_empty() {
                assert!(codes(&body, Checker::Polonius).is_empty(), "{}", body.name);
            }
        }
    }

    /// Our rendering is a prefix of rustc's (rustc may add notes and help).
    #[test]
    fn diagnostics_match_rustc_text() {
        let cases = [
            (
                "still_used",
                include_str!("../../../compile_fail/ch29_still_used.stderr"),
            ),
            (
                "conditional_move",
                include_str!("../../../compile_fail/ch29_conditional_move.stderr"),
            ),
            (
                "assign_while_borrowed",
                include_str!("../../../compile_fail/ch29_assign_while_borrowed.stderr"),
            ),
            (
                "rotate_top",
                include_str!("../../../compile_fail/ch29_two_phase_limit.stderr"),
            ),
        ];
        for (name, rustc) in cases {
            let body = by_name(name);
            let ours = check(&body, Checker::Nll)[0].render(&body);
            assert!(rustc.starts_with(&ours), "{name}:\n{ours}\nvs\n{rustc}");
        }
    }

    /// The region values of `record_count` are the ones rustc computes
    /// (`-Zdump-mir=nll`): `{bb1[3..=7], bb2[0..=1]}` for the `&mut` loan,
    /// `{bb1[6..=7]}` for the shared one.
    #[test]
    fn record_count_regions_match_rustc() {
        let body = record_count();
        let values = infer(&body, RegionMode::Nll).values;
        let loans = collect_loans(&body, true);
        let show = |r: RegionVid| describe_points(&values.points[r.0]).join(", ");
        assert_eq!(show(loans[0].region), "bb1[3..=7], bb2[0..=1]");
        assert_eq!(show(loans[1].region), "bb1[6..=7]");
        assert_eq!(
            loans[0].activation.map(|l| l.to_string()),
            Some("bb2[1]".into())
        );
    }

    #[test]
    fn drop_elaboration() {
        let styles = drop_styles(&maybe_archive());
        assert_eq!(styles.len(), 1);
        assert_eq!(styles[0].2, DropStyle::Conditional);
        assert_eq!(drop_styles(&record_count())[0].2, DropStyle::Dead);
        assert_eq!(drop_styles(&still_used())[0].2, DropStyle::Static);
    }

    #[test]
    fn nll_regions_are_contained_in_lexical_ones() {
        for body in all() {
            let nll = infer(&body, RegionMode::Nll).values;
            let lexical = infer(&body, RegionMode::Lexical).values;
            for (n, l) in nll.points.iter().zip(&lexical.points) {
                assert!(n.is_subset(l), "{}", body.name);
            }
        }
    }
}
