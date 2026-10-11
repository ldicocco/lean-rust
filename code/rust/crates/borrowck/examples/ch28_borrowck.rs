// harness: run
//! The two worked derivations of Chapter 28, produced by the `borrowck` crate:
//! derivation I (a `&mut` reference used twice, through two reborrows) is
//! printed as a tree; derivation II (the classic aliasing bug) is rejected,
//! and the error says which premise of which rule fails.
//!
//! Run with: `cargo run -p borrowck --example ch28_borrowck`

use borrowck::{check_program, parse_program};

// ANCHOR: twice
/// Derivation I. In Rust: `fn twice(r: &mut i32) { set(r, 1); set(r, 2); }`,
/// where each call passes an implicit reborrow `&mut *r`.
const TWICE: &str = "
fn twice<'a>(r: &'a mut Int) {
    let (r1, u1) = (borrow y1 = &'b1 mut *r in *y1 := 1) in
    let (r2, u2) = (borrow y2 = &'b2 mut *r1 in *y2 := 2) in
    ()
}";
// ANCHOR_END: twice

// ANCHOR: aliasing
/// Derivation II. In Rust: `let first = &v[0]; v.push(4); println!("{first}");`
const ALIASING: &str = "
fn aliasing(v: Box Int) {
    borrow f = &'a v in
      let (v2, u) = (borrow m = &'b mut v in *m := 4) in
      *f
}";
// ANCHOR_END: aliasing

// ANCHOR: main
fn main() {
    for src in [TWICE, ALIASING] {
        let program = parse_program(src).expect("the sample programs parse");
        let delta: Vec<String> =
            program.lifetimes.iter().map(|k| format!("'{k}")).collect();
        println!("== {} (Δ = {{{}}})", program.name, delta.join(", "));
        match check_program(&program) {
            Ok(derivation) => println!("{derivation}"),
            Err(error) => println!("{error}"),
        }
        println!();
    }
}
// ANCHOR_END: main
