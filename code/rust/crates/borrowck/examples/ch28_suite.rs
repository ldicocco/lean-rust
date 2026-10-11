// harness: run
//! A small test suite for the borrow calculus of Chapter 28: programs the
//! checker accepts and programs it rejects, each next to the rustc error code
//! of the corresponding real Rust program.
//!
//! Run with: `cargo run -p borrowck --example ch28_suite`

use borrowck::{check_program, parse_program};

// ANCHOR: programs
/// Each program is preceded by rustc's verdict on the corresponding Rust
/// program: `ok`, or the error code it reports.
const SUITE: &str = "
// rustc: ok
fn twice<'a>(r: &'a mut Int) {
    let (r1, u1) = (borrow y1 = &'b1 mut *r in *y1 := 1) in
    let (r2, u2) = (borrow y2 = &'b2 mut *r1 in *y2 := 2) in ()
}
// rustc: E0502
fn aliasing(v: Box Int) {
    borrow f = &'a v in let (v2, u) = (borrow m = &'b mut v in *m := 4) in *f
}
// rustc: ok
fn read_then_push(v: Box Int) {
    let (v, n) = (borrow f = &'a v in *f) in
    let (v, u) = (borrow m = &'b mut v in *m := 4) in n
}
// rustc: E0499
fn two_mut(v: Box Int) {
    borrow m1 = &'a mut v in borrow m2 = &'b mut v in *m1 := 1
}
// rustc: E0505
fn dangling(b: Box Int) {
    let (b, r) = (borrow y = &'a b in y) in let u = drop b in *r
}
// rustc: E0505
fn drop_while_borrowed(b: Box Int) { borrow y = &'a b in let u = drop b in *y }
// rustc: E0382
fn use_after_move(b: Box Int) { let c = b in (b, c) }
// rustc: ok
fn share<'a>(s: &'a Int) { (s, s) }
// rustc: E0507
fn move_out<'a>(s: &'a Box Int) { *s }
// rustc: E0594
fn write_shared<'a>(s: &'a Int) { *s := 1 }
";
// ANCHOR_END: programs

fn main() {
    println!("{:<20} {:<7} the calculus", "program", "rustc");
    // Each chunk is "<verdict>\n<program>".
    for chunk in SUITE.split("// rustc: ").skip(1) {
        let (rustc, src) = chunk.split_once('\n').expect("a verdict line");
        let program = parse_program(src).expect("the sample programs parse");
        let verdict = match check_program(&program) {
            Ok(derivation) => format!("ok: {}", derivation.conclusion.ty),
            Err(error) => error.headline(),
        };
        println!("{:<20} {:<7} {verdict}", program.name, rustc);
    }
}
