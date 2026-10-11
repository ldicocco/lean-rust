// harness: run
//! `branch_borrow` through the whole borrow checker: loans, liveness,
//! constraints, regions, loans in scope, and the verdicts.
//!
//! Run with: `cargo run -p mini-nll --example ch29_walkthrough`

use mini_nll::borrowck::{Checker, check, collect_loans, loans_in_scope};
use mini_nll::dataflow::solve;
use mini_nll::liveness::Liveness;
use mini_nll::mir::{Local, Location};
use mini_nll::programs;
use mini_nll::regions::{RegionMode, describe_points, infer};

fn main() {
    let body = programs::branch_borrow();
    let loans = collect_loans(&body, true);
    for (i, loan) in loans.iter().enumerate() {
        println!("L{i} = {}", body.fmt_rvalue_of_loan(loan));
    }
    // Where is `tail` (_3) live?
    let live = solve(&body, Liveness).states_before(&body);
    let tail_live = live
        .iter()
        .filter(|(_, locals)| locals.contains(&Local(3)))
        .map(|(loc, _)| *loc)
        .collect();
    println!(
        "tail (_3) live at {{{}}}",
        describe_points(&tail_live).join(", ")
    );
    let nll = infer(&body, RegionMode::Nll);
    for c in &nll.constraints {
        let (sup, sub) = (body.region_name(c.sup), body.region_name(c.sub));
        println!("constraint {sup}: {sub} at {}", c.location);
    }
    let push_else = Location {
        block: body.block_ids().nth(4).unwrap(),
        index: 2,
    };
    println!("log.push(2) borrows `log` at {push_else}");
    for (mode, checker) in [
        (RegionMode::Nll, Checker::Nll),
        (RegionMode::Lexical, Checker::Lexical),
    ] {
        let values = infer(&body, mode).values;
        let in_scope = loans_in_scope(&body, &loans, &values);
        let names: Vec<String> = in_scope[&push_else]
            .iter()
            .map(|l| format!("L{l}"))
            .collect();
        println!("{}:", checker.name());
        println!(
            "  region of L0 = {}",
            values.describe(&body, loans[0].region)
        );
        println!("  loans in scope at {push_else}: {{{}}}", names.join(", "));
        let diags = check(&body, checker);
        println!("  {} error(s)", diags.len());
        for d in diags {
            print!("{}", d.render(&body));
        }
    }
}
