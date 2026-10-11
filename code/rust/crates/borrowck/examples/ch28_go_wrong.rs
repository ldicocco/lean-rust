// harness: run
//! What the type system of Chapter 28 prevents: two programs that the checker
//! rejects, run anyway. Each one reaches a state in which no rule of the
//! semantics applies: the machine is stuck, the formal version of undefined
//! behavior.
//!
//! Run with: `cargo run -p borrowck --example ch28_go_wrong`

use borrowck::{Machine, Outcome, check_program, parse_program};

// ANCHOR: programs
/// A reference escapes its borrow and is used after the owner is dropped.
const DANGLING: &str = "
fn dangling() {
    let b = new 5 in
    let (b, r) = (borrow y = &'a b in y) in
    let u = drop b in
    *r
}";

/// Derivation II, closed: the owner is created by the program itself.
const ALIASING: &str = "
fn aliasing() {
    let v = new 1 in
    borrow f = &'a v in
      let (v2, u) = (borrow m = &'b mut v in *m := 4) in
      *f
}";
// ANCHOR_END: programs

fn main() {
    for src in [DANGLING, ALIASING] {
        let program = parse_program(src).expect("the sample programs parse");
        println!("== {}", program.name);
        let error = check_program(&program).expect_err("the checker rejects it");
        println!("{}", error.headline());
        println!("-- run without checking:");
        let mut machine = Machine::default();
        let (trace, outcome) = machine.run(program.body, 100);
        for (i, step) in trace.iter().enumerate() {
            println!("{:>2}  {:<14} {}", i + 1, step.rule, step.store);
        }
        match outcome {
            Outcome::Value(v) => println!("value: {v}"),
            Outcome::Stuck(stuck) => println!("{stuck}"),
            Outcome::OutOfFuel => println!("out of fuel"),
        }
        println!();
    }
}
