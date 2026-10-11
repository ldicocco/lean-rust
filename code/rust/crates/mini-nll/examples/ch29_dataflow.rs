// harness: run
//! Three dataflow analyses on `maybe_archive`, drop elaboration, and the E0382
//! check on `conditional_move`.
//!
//! Run with: `cargo run -p mini-nll --example ch29_dataflow`

use std::collections::BTreeSet;
use std::fmt::Display;

use mini_nll::dataflow::{Analysis, solve};
use mini_nll::liveness::Liveness;
use mini_nll::mir::Body;
use mini_nll::moves::{MaybeInit, MaybeUninit, check_moves, drop_styles};
use mini_nll::programs;

fn set<T: Display>(s: &BTreeSet<T>) -> String {
    let items: Vec<String> = s.iter().map(|x| x.to_string()).collect();
    format!("{{{}}}", items.join(", "))
}

// ANCHOR: run_analysis
/// Solve `analysis` on `body` and print the state at the entry of every
/// block (for a backward analysis: at the exit, where it starts).
fn show<A, T>(body: &Body, title: &str, analysis: A)
where
    A: Analysis<Domain = BTreeSet<T>>,
    T: Display,
{
    let results = solve(body, analysis);
    println!("{title} ({} block visits)", results.block_visits);
    for (bb, state) in body.block_ids().zip(&results.block_states) {
        println!("  {bb}: {}", set(state));
    }
}
// ANCHOR_END: run_analysis

fn main() {
    let body = programs::maybe_archive();
    show(&body, "maybe-uninitialized, on entry", MaybeUninit);
    show(&body, "maybe-initialized, on entry", MaybeInit);
    show(&body, "live, on exit", Liveness);
    println!("drop elaboration:");
    for program in [programs::maybe_archive(), programs::record_count()] {
        for (loc, place, style) in drop_styles(&program) {
            println!("  {}: {loc} drop({place}) is {style:?}", program.name);
        }
    }
    println!();
    let body = programs::conditional_move();
    for d in check_moves(&body) {
        print!("{}", d.render(&body));
    }
}
