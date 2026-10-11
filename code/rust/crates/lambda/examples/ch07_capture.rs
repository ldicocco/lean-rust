// harness: run
//! Variable capture: a naive substitution changes the meaning of a program;
//! capture-avoiding substitution and de Bruijn indices do not.
//!
//! Run with: `cargo run -p lambda --example ch07_capture`

use lambda::{DbTerm, Strategy, Term, app, lam, parse, reduce, to_de_bruijn};

// ANCHOR: naive
/// Textual replacement of `x` by `s`, stopping only at a `λx` that shadows
/// `x`. This is WRONG: it does not check whether a `λ` captures a free
/// variable of `s`.
fn naive_subst(t: &Term, x: &str, s: &Term) -> Term {
    match t {
        Term::Var(y) if y == x => s.clone(),
        Term::Var(_) => t.clone(),
        Term::Lam(y, _) if y == x => t.clone(),
        Term::Lam(y, body) => lam(y, naive_subst(body, x, s)),
        Term::App(f, a) => app(naive_subst(f, x, s), naive_subst(a, x, s)),
    }
}
// ANCHOR_END: naive

/// Normal-order reduction using the naive substitution.
fn naive_step(t: &Term) -> Option<Term> {
    match t {
        Term::Var(_) => None,
        Term::Lam(x, body) => naive_step(body).map(|b| lam(x, b)),
        Term::App(f, a) => {
            if let Term::Lam(x, body) = &**f {
                return Some(naive_subst(body, x, a));
            }
            if let Some(f2) = naive_step(f) {
                return Some(app(f2, (**a).clone()));
            }
            naive_step(a).map(|a2| app((**f).clone(), a2))
        }
    }
}

fn naive_normalize(t: &Term) -> Term {
    let mut t = t.clone();
    while let Some(next) = naive_step(&t) {
        t = next;
    }
    t
}

fn p(src: &str) -> Term {
    parse(src).unwrap()
}

fn main() {
    // ANCHOR: substitution
    let body = p("λy. x");
    let s = p("y");
    println!("({body})[x := {s}]");
    println!("  naive:            {}", naive_subst(&body, "x", &s));
    println!("  capture-avoiding: {}", body.subst("x", &s));
    // ANCHOR_END: substitution

    // ANCHOR: reduction
    // K = λx. λy. x returns its first argument, so K y z must be y.
    let program = p("(λx. λy. x) y z");
    println!("\n{program}");
    let wrong = naive_normalize(&program);
    let right = reduce(&program, Strategy::NormalOrder, 100).term;
    println!("  with naive substitution:            {wrong}");
    println!("  with capture-avoiding substitution: {right}");
    assert_eq!(wrong, p("z"));
    assert_eq!(right, p("y"));
    // ANCHOR_END: reduction

    // ANCHOR: de_bruijn
    // The same β-step with de Bruijn indices. The naming context is [y]: the
    // free variable y is index 0 outside every binder.
    let redex = to_de_bruijn(&p("(λx. λy. x) y"), &["y"]).unwrap();
    println!("\n(λx. λy. x) y  is  {redex}  in the naming context [y]");
    let DbTerm::App(f, arg) = &redex else {
        unreachable!()
    };
    let DbTerm::Lam(k_body) = &**f else {
        unreachable!()
    };
    println!("  with the shift:    {}", k_body.subst(0, arg));
    println!(
        "  without the shift: {}",
        k_body.subst_without_shift(0, arg)
    );
    // ANCHOR_END: de_bruijn

    // ANCHOR: alpha
    println!("\nα-equivalence is equality of de Bruijn terms:");
    for src in ["λx. λy. x", "λa. λb. a", "λx. λy. y", "λy. λx. y"] {
        let t = p(src);
        let db = to_de_bruijn(&t, &[]).unwrap().to_string();
        let same = t.alpha_eq(&p("λx. λy. x"));
        println!("  {src:<10} ↦ {db:<10} α-equivalent to λx. λy. x: {same}");
    }
    // ANCHOR_END: alpha
}
