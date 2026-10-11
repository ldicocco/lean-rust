//! A type checker for the affine lambda calculus, with Copy types.
//!
//! Built in Chapter 22 (the affine calculus λ^aff: moves, context splitting,
//! errors modeled on rustc's E0382) and extended in Chapter 23 (`Copy` types,
//! `Clone`, `Rc`, and the checks on `#[derive(Copy)]`).
//!
//! The input language is λ^aff written with Rust-like syntax:
//!
//! ```text
//! fn close(f: File);                                  // provided by the environment
//!
//! fn swap(p: (String, File)) -> (File, String) {     // Γ = p : (String, File)
//!     let (s, f) = p;                                 // ⊗ elimination
//!     (f, s)                                          // ⊗ introduction
//! }
//! ```
//!
//! [`check_source`] parses and checks a program; [`render`] prints the
//! derivations of the functions that check and the errors of those that do
//! not, in the format of rustc.

pub mod check;
pub mod copy;
pub mod derivation;
pub mod diagnostic;
pub mod parser;
pub mod syntax;

pub use check::{Report, check_program};
pub use copy::Discipline;
pub use derivation::Derivation;
pub use diagnostic::Diagnostic;

/// Parse and check a program. A syntax error is returned as `Err`.
pub fn check_source(src: &str, discipline: Discipline) -> Result<Report, Diagnostic> {
    let program = parser::parse_program(src)?;
    Ok(check_program(&program, discipline))
}

/// What to print for the functions that check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Show {
    /// Only `ok: fn ...` lines.
    Verdicts,
    /// The full derivation of each function.
    Derivations,
    /// The derivations, with the contexts shown as variable names only.
    Compact,
}

/// Check a program and render the result: for each function that checks, its
/// signature (and derivation); then every error, as rustc would print it.
pub fn render(file: &str, src: &str, discipline: Discipline, show: Show) -> String {
    let report = match check_source(src, discipline) {
        Ok(report) => report,
        Err(d) => return d.render(file, src),
    };
    let mut out = String::new();
    for f in &report.functions {
        out += &format!("ok: {}\n", f.signature);
        match show {
            Show::Verdicts => {}
            Show::Derivations => out += &f.derivation.render(),
            Show::Compact => out += &f.derivation.render_compact(),
        }
        if !f.dropped.is_empty() && show != Show::Verdicts {
            out += &format!("    (discarded without use: {})\n", f.dropped.join(", "));
        }
    }
    for (i, d) in report.errors.iter().enumerate() {
        if i > 0 {
            out += "\n";
        }
        out += &d.render(file, src);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn errors(src: &str, discipline: Discipline) -> Vec<String> {
        let report = check_source(src, discipline).expect("parses");
        report
            .errors
            .iter()
            .map(|d| format!("{}: {}", d.code.clone().unwrap_or_default(), d.message))
            .collect()
    }

    fn accepts(src: &str, discipline: Discipline) -> bool {
        errors(src, discipline).is_empty()
    }

    const DECLS: &str = "
        fn close(f: File);
        fn send(c: Conn, s: String) -> Conn;
        fn buy_coffee(c: Coin) -> Coffee;
        fn buy_tea(c: Coin) -> Tea;
    ";

    fn with_decls(src: &str) -> String {
        format!("{DECLS}\n{src}")
    }

    #[test]
    fn swap_and_discard_check() {
        let src = with_decls(
            "fn swap(p: (String, File)) -> (File, String) { let (s, f) = p; (f, s) }
             fn first(s: String, f: File) -> String { s }
             fn forget(s: String) -> () { () }",
        );
        let report = check_source(&src, Discipline::Affine).unwrap();
        assert!(report.errors.is_empty());
        assert_eq!(report.functions.len(), 3);
        assert_eq!(report.functions[1].dropped, ["f"]);
        let swap = &report.functions[0].derivation;
        assert_eq!(swap.rule, "A-LetPair");
        assert_eq!(swap.size(), 5);
        assert_eq!(
            swap.premises[1].judgment(),
            "s: String, f: File ⊢ (f, s) : (File, String)"
        );
    }

    #[test]
    fn duplication_is_rejected() {
        let e = errors(
            "fn dup(s: String) -> (String, String) { (s, s) }",
            Discipline::Affine,
        );
        assert_eq!(e, ["E0382: use of moved value: `s`"]);
        let e = errors(
            &with_decls(
                "fn both(c: Coin) -> (Coffee, Tea) { (buy_coffee(c), buy_tea(c)) }",
            ),
            Discipline::Affine,
        );
        assert_eq!(e, ["E0382: use of moved value: `c`"]);
    }

    #[test]
    fn additive_rules_share_the_context() {
        let src = with_decls(
            "fn offer(c: Coin) -> With<Coffee, Tea> { with(buy_coffee(c), buy_tea(c)) }
             fn pick(c: Coin) -> Tea { let w = offer(c); w.snd }
             fn route(m: Either<String, String>, c: Conn) -> Conn {
                 match m { Left(a) => send(c, a), Right(b) => send(c, b) }
             }",
        );
        assert!(accepts(&src, Discipline::Affine));
        // ...but a variable moved in one arm is moved after the match.
        let src = with_decls(
            "fn route(m: Either<String, String>, c: Conn, s: String) -> (Conn, String) {
                 let c = match m { Left(a) => send(c, s), Right(b) => send(c, b) };
                 (c, s)
             }",
        );
        assert_eq!(
            errors(&src, Discipline::Affine),
            ["E0382: use of moved value: `s`"]
        );
    }

    #[test]
    fn partial_moves_are_tracked_per_place() {
        let ok = "fn swap(p: (String, File)) -> (File, String) { (p.1, p.0) }";
        assert!(accepts(ok, Discipline::Affine));
        let bad = "fn f(p: (String, File)) -> (String, (String, File)) { let a = p.0; (a, p) }";
        assert_eq!(
            errors(bad, Discipline::Affine),
            ["E0382: use of partially moved value: `p`"]
        );
        let bad = "fn f(p: (String, File)) -> (String, String) { (p.0, p.0) }";
        assert_eq!(
            errors(bad, Discipline::Affine),
            ["E0382: use of moved value: `p.0`"]
        );
    }

    #[test]
    fn closures_capture_and_are_called_once() {
        let src = with_decls(
            "fn later(c: Conn, s: String) -> FnOnce(()) -> Conn { |u: ()| send(c, s) }",
        );
        assert!(accepts(&src, Discipline::Affine));
        let src = with_decls(
            "fn capture(c: Conn, s: String) -> (FnOnce(()) -> Conn, String) {
                 let f = |u: ()| send(c, s);
                 (f, s)
             }",
        );
        assert_eq!(
            errors(&src, Discipline::Affine),
            ["E0382: use of moved value: `s`"]
        );
        let src = "fn twice(f: FnOnce(String) -> String, a: String, b: String) -> (String, String) {
                       (f(a), f(b))
                   }";
        assert_eq!(
            errors(src, Discipline::Affine),
            ["E0382: use of moved value: `f`"]
        );
    }

    #[test]
    fn copy_types_can_be_used_twice() {
        let src = "fn twice(n: i32) -> (i32, i32) { (n, n) }";
        assert_eq!(
            errors(src, Discipline::Affine),
            ["E0382: use of moved value: `n`"]
        );
        assert!(accepts(src, Discipline::Copy));
        let src = "#[derive(Clone, Copy)] struct Point { x: i32, y: i32 }
                   fn mirror(p: Point) -> (Point, (i32, i32)) { (p, (p.y, p.x)) }";
        assert!(accepts(src, Discipline::Copy));
        let src = "fn readers(r: &String) -> (&String, &String) { (r, r) }";
        assert!(accepts(src, Discipline::Copy));
        let src = "fn writers(w: &mut String) -> (&mut String, &mut String) { let a = w; (a, w) }";
        assert_eq!(
            errors(src, Discipline::Copy),
            ["E0382: use of moved value: `w`"]
        );
    }

    #[test]
    fn clone_is_explicit() {
        let src = "fn backup(s: String) -> (String, String) { (s.clone(), s) }";
        assert!(accepts(src, Discipline::Copy));
        assert_eq!(
            errors(src, Discipline::Affine),
            ["E0599: no method named `clone` found for `String` in the current scope"]
        );
        let src = "fn backup(f: File) -> (File, File) { (f.clone(), f) }";
        assert_eq!(
            errors(src, Discipline::Copy),
            ["E0599: no method named `clone` found for `File` in the current scope"]
        );
        let src =
            "fn share(c: Rc<Config>) -> (Rc<Config>, Rc<Config>) { (c.clone(), c) }";
        assert!(accepts(src, Discipline::Copy));
        let src = "fn share(c: Rc<Config>) -> (Rc<Config>, Rc<Config>) { (c, c) }";
        assert_eq!(
            errors(src, Discipline::Copy),
            ["E0382: use of moved value: `c`"]
        );
        let src =
            "fn late(s: String) -> (String, String) { let t = s; (t, s.clone()) }";
        assert_eq!(
            errors(src, Discipline::Copy),
            ["E0382: borrow of moved value: `s`"]
        );
    }

    #[test]
    fn copy_fields_do_not_move() {
        let src = "struct Reading { sensor: String, value: i32 }
                   fn values(r: Reading) -> ((i32, i32), Reading) { ((r.value, r.value), r) }";
        assert!(accepts(src, Discipline::Copy));
        let src = "struct Reading { sensor: String, value: i32 }
                   fn name(r: Reading) -> (String, Reading) { (r.sensor, r) }";
        assert_eq!(
            errors(src, Discipline::Copy),
            ["E0382: use of partially moved value: `r`"]
        );
    }

    #[test]
    fn type_errors() {
        let e = errors("fn f(s: String) -> File { s }", Discipline::Affine);
        assert_eq!(e, ["E0308: mismatched types"]);
        let e = errors("fn f(s: String) -> String { t }", Discipline::Affine);
        assert_eq!(e, ["E0425: cannot find value `t` in this scope"]);
        let e = errors(
            "fn f(s: String) -> Either<String, File> { let x = Left(s); x }",
            Discipline::Affine,
        );
        assert_eq!(e, ["E0282: type annotations needed"]);
        let e = errors(
            "fn f(s: String) -> Either<String, File> { let x: Either<String, File> = Left(s); x }",
            Discipline::Affine,
        );
        assert!(e.is_empty());
    }

    /// The checker agrees with the usage theorem: in every function it
    /// accepts, a non-Copy variable occurs at most once on every path.
    #[test]
    fn leftovers_mark_exactly_the_moved_variables() {
        let src = with_decls(
            "fn keep(c: Conn, s: String, t: String) -> (Conn, String) { (send(c, s), t) }",
        );
        let report = check_source(&src, Discipline::Affine).unwrap();
        let d = &report.functions[0].derivation;
        // The whole derivation uses c, s and t; its first premise c and s.
        assert_eq!(d.ctx.len(), 3);
        let first: Vec<&str> =
            d.premises[0].ctx.iter().map(|(x, _)| x.as_str()).collect();
        assert_eq!(first, ["c", "s"]);
    }

    #[test]
    fn renders_errors_and_derivations() {
        let src = "fn dup(s: String) -> (String, String) {\n    (s, s)\n}\n";
        let out = render("dup.aff", src, Discipline::Affine, Show::Derivations);
        assert!(
            out.starts_with(
                "error[E0382]: use of moved value: `s`\n --> dup.aff:2:9\n"
            )
        );
        let src = "fn id(s: String) -> String { s }";
        let out = render("id.aff", src, Discipline::Affine, Show::Derivations);
        assert_eq!(
            out,
            "ok: fn id(s: String) -> String\n[A-Var] s: String ⊢ s : String\n"
        );
    }
}
