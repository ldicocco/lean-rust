// harness: run
//! Real Rust that the borrow checker accepts thanks to non-lexical lifetimes
//! and two-phase borrows, plus the usual workarounds for NLL problem case #3.
//!
//! The functions `first_then_push`, `maybe_archive`, `record_count` and
//! `branch_borrow` are the ones whose MIR `mini-nll` builds by hand in
//! Chapter 29.
//!
//! Run with: `cargo run --example ch29_nll_accepts`

use std::collections::HashMap;

fn archive(job: String) -> usize {
    job.len()
}

// ANCHOR: first_then_push
/// The borrow `first` is last used before the push: NLL accepts this, a
/// lexical borrow checker (Rust before 2018) rejected it.
fn first_then_push() -> usize {
    let mut readings = vec![10, 20, 30];
    let first = &readings[0];
    println!("first = {first}");
    readings.push(40);
    readings.len()
}
// ANCHOR_END: first_then_push

// ANCHOR: maybe_archive
/// `job` is moved on one path only, so at the end of the function it is
/// "maybe initialized": the compiler drops it under a run-time drop flag.
fn maybe_archive(urgent: bool) {
    let job = String::from("backup");
    if urgent {
        archive(job);
    }
}
// ANCHOR_END: maybe_archive

// ANCHOR: record_count
/// `counts.push(counts.len())`: the receiver is borrowed mutably *before* the
/// argument is evaluated. Two-phase borrows make this legal.
fn record_count() -> Vec<usize> {
    let mut counts = Vec::new();
    counts.push(counts.len());
    counts
}
// ANCHOR_END: record_count

// ANCHOR: branch_borrow
/// `tail` is used on one branch only; on the other branch it is dead, so its
/// loan is not in scope there (NLL "problem case #2").
fn branch_borrow(verbose: bool) -> Vec<u32> {
    let mut log = Vec::new();
    let tail = &mut log;
    if verbose {
        tail.push(1);
    } else {
        log.push(2);
    }
    log
}
// ANCHOR_END: branch_borrow

// ANCHOR: two_phase_more
/// More two-phase borrows: an implicit reborrow of a `&mut` argument, and the
/// mutable borrow behind an overloaded `+=`.
fn put(dst: &mut Vec<usize>, n: usize) {
    dst.push(n);
}

fn more_two_phase(v: &mut Vec<usize>) -> String {
    put(v, v.len()); // `v` is reborrowed as `&mut *v` (two-phase)
    v.push(*v.last().unwrap()); // shared reads before the activation are fine
    let mut banner = String::from("ab");
    banner += &banner.to_uppercase(); // `AddAssign::add_assign(&mut banner, ..)`
    banner
}
// ANCHOR_END: two_phase_more

// ANCHOR: workarounds
/// Problem case #3 rewritten so that NLL accepts it: look the key up twice.
fn get_default_twice<'r>(
    cache: &'r mut HashMap<u32, String>,
    key: u32,
) -> &'r mut String {
    if !cache.contains_key(&key) {
        cache.insert(key, String::new());
    }
    cache.get_mut(&key).unwrap()
}

/// The idiomatic version: the entry API does the case analysis inside the
/// library, behind a single mutable borrow.
fn get_default_entry<'r>(
    cache: &'r mut HashMap<u32, String>,
    key: u32,
) -> &'r mut String {
    cache.entry(key).or_default()
}
// ANCHOR_END: workarounds

fn main() {
    println!("first_then_push() = {}", first_then_push());
    maybe_archive(true);
    maybe_archive(false);
    println!("record_count() = {:?}", record_count());
    println!("branch_borrow(true) = {:?}", branch_borrow(true));
    println!("branch_borrow(false) = {:?}", branch_borrow(false));

    let mut v = vec![7];
    let banner = more_two_phase(&mut v);
    println!("more_two_phase: v = {v:?}, banner = {banner}");
    assert_eq!(v, vec![7, 1, 1]);
    assert_eq!(banner, "abAB");

    let mut cache = HashMap::new();
    get_default_twice(&mut cache, 1).push_str("one");
    get_default_entry(&mut cache, 2).push_str("two");
    get_default_entry(&mut cache, 1).push('!');
    let mut entries: Vec<_> = cache.into_iter().collect();
    entries.sort();
    println!("cache = {entries:?}");
}
