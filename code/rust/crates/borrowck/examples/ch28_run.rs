// harness: run
//! The operational semantics of Chapter 28 at work: a well-typed program that
//! borrows an owner mutably, reborrows the reference twice, reads the result
//! through a shared borrow and frees the owner. Each line of the trace shows
//! the rule applied and the store after the step, with the loan state of each
//! location.
//!
//! Run with: `cargo run -p borrowck --example ch28_run`

use borrowck::{Machine, Outcome, check_program, parse_program};

// ANCHOR: program
const PROGRAM: &str = "
fn main() {
    let b = new 0 in
    let (b, u) = (borrow r = &'a mut b in
                    let (r1, u1) = (borrow y1 = &'b1 mut *r in *y1 := 1) in
                    let (r2, u2) = (borrow y2 = &'b2 mut *r1 in *y2 := 2) in
                    ()) in
    let (b, n) = (borrow s = &'c b in *s) in
    let u = drop b in
    n
}";
// ANCHOR_END: program

fn main() {
    let program = parse_program(PROGRAM).expect("the program parses");
    let derivation = check_program(&program).expect("the program is well typed");
    println!("type: {}", derivation.conclusion.ty);
    // ANCHOR: run
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
    // ANCHOR_END: run
}
