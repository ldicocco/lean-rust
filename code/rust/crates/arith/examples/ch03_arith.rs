// harness: run
//! Arith in action: parse sample programs, search for typing derivations,
//! print them as indented trees, and run the programs.
//!
//! Run with: `cargo run -p arith --example ch03_arith`

use arith::{Ctx, Env, check, eval, parse};

// ANCHOR: show_derivation
/// Type check a closed program, print its derivation, then run it.
fn show_derivation(src: &str) {
    let e = parse(src).expect("the samples are syntactically valid");
    let d = check(&Ctx::new(), &e).expect("this sample is well typed");
    assert!(d.verify(), "the checker only builds valid derivations");
    print!("{}", d.render());
    let v = eval(&Env::new(), &e).expect("well-typed programs do not go wrong");
    assert_eq!(v.ty(), d.ty());
    println!("({} rules, height {}; value {v})", d.size(), d.height());
    println!();
}
// ANCHOR_END: show_derivation

// ANCHOR: show_rejection
/// Type check a program that should be rejected, and see what running it
/// anyway would do.
fn show_rejection(src: &str) {
    let e = parse(src).expect("the samples are syntactically valid");
    let err = check(&Ctx::new(), &e).expect_err("this sample is ill typed");
    println!("{src}");
    println!("  type error: {err}");
    match eval(&Env::new(), &e) {
        Ok(v) => println!("  if run anyway: value {v}"),
        Err(stuck) => println!("  if run anyway: {stuck}"),
    }
}
// ANCHOR_END: show_rejection

fn main() {
    // ANCHOR: samples
    show_derivation("1 + 2");
    show_derivation("let x = 3 in if x == 3 then x + 1 else 0");
    show_derivation("let x = true in let x = 5 in x + 1");

    show_rejection("1 + true");
    show_rejection("if 1 then 2 else 3");
    show_rejection("let x = 1 in y");
    show_rejection("if 1 == 1 then 1 else false");
    // ANCHOR_END: samples

    // ANCHOR: overflow
    // Well typed, and still the run fails: Arith's Nat is unbounded, but this
    // implementation stores it in a u64. Types say nothing about overflow.
    let src = "18446744073709551615 + 1";
    let e = parse(src).unwrap();
    let ty = check(&Ctx::new(), &e).map(|d| d.ty());
    println!();
    println!("{src}");
    println!("  type: {}", ty.unwrap());
    println!("  run: {}", eval(&Env::new(), &e).unwrap_err());
    // ANCHOR_END: overflow
}
