// harness: run
//! Two-phase borrows: `counts.push(counts.len())` with and without them, and
//! `stack.push(stack.pop().unwrap())`, which two-phase borrows do not save.
//!
//! Run with: `cargo run -p mini-nll --example ch29_two_phase`

use mini_nll::borrowck::{Checker, check, collect_loans};
use mini_nll::mir::BorrowKind;
use mini_nll::programs;

fn main() {
    let body = programs::record_count();
    for (i, loan) in collect_loans(&body, true).iter().enumerate() {
        let activation = match (loan.kind, loan.activation) {
            (BorrowKind::TwoPhaseMut, Some(at)) => {
                format!(", two-phase, activated at {at}")
            }
            _ => String::new(),
        };
        println!("L{i} = {}{activation}", body.fmt_rvalue_of_loan(loan));
    }
    for checker in [Checker::NllWithoutTwoPhase, Checker::Nll] {
        let diags = check(&body, checker);
        println!("record_count, {}: {} error(s)", checker.name(), diags.len());
        for d in diags {
            print!("{}", d.render(&body));
        }
    }
    let body = programs::rotate_top();
    let diags = check(&body, Checker::Nll);
    println!("rotate_top, NLL: {} error(s)", diags.len());
    for d in diags {
        print!("{}", d.render(&body));
    }
}
