// harness: run
//! NLL problem case #3: NLL rejects `get_default`, the location-sensitive
//! (Polonius-style) analysis accepts it. Shows where the first loan lives.
//!
//! Run with: `cargo run -p mini-nll --example ch29_polonius`

use mini_nll::borrowck::{Checker, check, collect_loans};
use mini_nll::mir::Location;
use mini_nll::polonius;
use mini_nll::programs;
use mini_nll::regions::{RegionMode, infer, outlives_constraints};

fn main() {
    let body = programs::problem_case_3();
    let loans = collect_loans(&body, true);
    let l0 = &loans[0];
    println!("L0 = {}", body.fmt_rvalue_of_loan(l0));

    // NLL: one region per loan, a set of points.
    let values = infer(&body, RegionMode::Nll).values;
    println!("NLL: region of L0 = {}", values.describe(&body, l0.region));
    let diags = check(&body, Checker::Nll);
    println!("NLL: {} errors; the first one:", diags.len());
    print!("{}", diags[0].render(&body));

    // Polonius: per point, which live origins contain L0?
    let constraints = outlives_constraints(&body);
    let (facts, live) = polonius::facts(&body, &loans, &constraints);
    // ANCHOR: holders
    // The live origins that contain L0 on entry to `loc`: `loan_live_at`.
    let holders = |loc: Location| -> String {
        let origins: Vec<String> = facts[&loc]
            .contains
            .iter()
            .filter(|(o, l)| *l == 0 && live[&loc].contains(o))
            .map(|(o, _)| body.region_name(*o))
            .collect();
        if origins.is_empty() {
            "-".to_string()
        } else {
            origins.join(", ")
        }
    };
    // ANCHOR_END: holders
    println!("Polonius: live origins containing L0, on entry to each block");
    for bb in body.block_ids() {
        let loc = Location {
            block: bb,
            index: 0,
        };
        println!("  {bb}: {:<5} {}", holders(loc), body.fmt_location(loc));
    }
    println!("Polonius: inside bb2 (the `Some` arm)");
    for index in 1..=4 {
        let loc = Location {
            block: body.block_ids().nth(2).unwrap(),
            index,
        };
        println!("  {loc}: {:<5} {}", holders(loc), body.fmt_location(loc));
    }
    println!("Polonius: {} errors", check(&body, Checker::Polonius).len());
}
