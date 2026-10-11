//! Hindley-Milner type inference: algorithm W, with the substitution kept in
//! a mutable table (the formulation Milner called algorithm J, and the one
//! rustc's inference engine also uses).
//!
//! The textbook algorithm W returns a substitution together with a type and
//! composes substitutions at every step. Here the substitution lives in one
//! `Subst` table that only ever grows; "composing" a new substitution after
//! the current one is just adding its bindings to the table. The two
//! formulations compute the same principal types.

use std::collections::BTreeSet;

use crate::diagnostic::Diagnostic;
use crate::syntax::{Expr, ExprKind};
use crate::types::{Namer, Scheme, TyCon, TyVar, Type, show_with};
use crate::unify::{Subst, UnifyError};

/// How a name in the environment was bound. Error messages use it to explain
/// why a variable is, or is not, polymorphic.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Origin {
    Prelude,
    /// A parameter of `fun`: always monomorphic.
    Lambda,
    /// A `let`. `blocked` is true when some type variables could not be
    /// generalized because the environment mentions them.
    Let {
        blocked: bool,
    },
    /// A `let rec` function, seen from inside its own definition.
    Recursive,
}

struct Binding {
    name: String,
    scheme: Scheme,
    origin: Origin,
}

/// The state of one run of inference: the substitution and the environment.
pub struct Infer<'src> {
    source: &'src str,
    subst: Subst,
    env: Vec<Binding>,
    trace: Option<Vec<String>>,
}

/// The principal type scheme of a closed mini-ML program, or the first type
/// error, as a diagnostic that `Diagnostic::render` turns into a message.
pub fn infer_program(source: &str) -> Result<Scheme, Diagnostic> {
    let expr = crate::parser::parse(source)?;
    Infer::new(source).run(&expr)
}

/// Like `infer_program`, and also returns a trace of the algorithm's steps.
pub fn trace_program(source: &str) -> (Vec<String>, Result<Scheme, Diagnostic>) {
    let expr = match crate::parser::parse(source) {
        Ok(expr) => expr,
        Err(diag) => return (vec![], Err(diag)),
    };
    let mut infer = Infer::new(source);
    infer.trace = Some(Vec::new());
    infer.subst.start_trace();
    let result = infer.run(&expr);
    (renumber(infer.trace.unwrap_or_default()), result)
}

// ANCHOR: prelude
impl<'src> Infer<'src> {
    /// A fresh inference run, with the prelude in the environment.
    pub fn new(source: &'src str) -> Infer<'src> {
        let mut infer = Infer {
            source,
            subst: Subst::new(),
            env: Vec::new(),
            trace: None,
        };
        let (int, bool) = (Type::int, Type::bool);
        let arith = || Type::fun(int(), Type::fun(int(), int()));
        let compare = || Type::fun(int(), Type::fun(int(), bool()));
        for op in ["+", "-", "*"] {
            infer.builtin(op, 0, |_| arith());
        }
        for op in ["==", "<"] {
            infer.builtin(op, 0, |_| compare());
        }
        infer.builtin("not", 0, |_| Type::fun(bool(), bool()));
        infer.builtin("fst", 2, |v| {
            Type::fun(Type::pair(v[0].clone(), v[1].clone()), v[0].clone())
        });
        infer.builtin("snd", 2, |v| {
            Type::fun(Type::pair(v[0].clone(), v[1].clone()), v[1].clone())
        });
        infer.builtin("nil", 1, |v| Type::list(v[0].clone()));
        infer.builtin("cons", 1, |v| {
            let list = Type::list(v[0].clone());
            Type::fun(v[0].clone(), Type::fun(list.clone(), list))
        });
        infer.builtin("head", 1, |v| {
            Type::fun(Type::list(v[0].clone()), v[0].clone())
        });
        infer.builtin("tail", 1, |v| {
            Type::fun(Type::list(v[0].clone()), Type::list(v[0].clone()))
        });
        infer.builtin("null", 1, |v| Type::fun(Type::list(v[0].clone()), bool()));
        infer
    }

    /// Adds a prelude function whose scheme quantifies over `n` variables.
    fn builtin(&mut self, name: &str, n: usize, ty: impl Fn(&[Type]) -> Type) {
        let vars: Vec<TyVar> = (0..n).map(|_| self.subst.fresh()).collect();
        let args: Vec<Type> = vars.iter().map(|v| Type::Var(*v)).collect();
        let scheme = Scheme {
            vars,
            ty: ty(&args),
        };
        self.env.push(Binding {
            name: name.to_string(),
            scheme,
            origin: Origin::Prelude,
        });
    }
}
// ANCHOR_END: prelude

// ANCHOR: generalize
impl Infer<'_> {
    /// The type variables free in the environment: those of every binding's
    /// type (after applying the substitution), minus the binding's own
    /// quantified variables.
    fn env_vars(&self) -> BTreeSet<TyVar> {
        let mut vars = BTreeSet::new();
        for binding in &self.env {
            for v in self.subst.apply(&binding.scheme.ty).vars() {
                if !binding.scheme.vars.contains(&v) {
                    vars.insert(v);
                }
            }
        }
        vars
    }

    /// Gen(Γ, τ) = forall (ftv(τ) \ ftv(Γ)). τ
    /// Also reports whether some variable was kept monomorphic because the
    /// environment mentions it.
    fn generalize(&self, ty: &Type) -> (Scheme, bool) {
        let ty = self.subst.apply(ty);
        let in_env = self.env_vars();
        let (vars, blocked): (Vec<TyVar>, Vec<TyVar>) =
            ty.vars().into_iter().partition(|v| !in_env.contains(v));
        (Scheme { vars, ty }, !blocked.is_empty())
    }

    /// Inst(forall a1 ... an. τ) = τ[a1 := ?1, ..., an := ?n], with fresh ?i.
    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let fresh: Vec<(TyVar, Type)> = scheme
            .vars
            .iter()
            .map(|v| (*v, Type::Var(self.subst.fresh())))
            .collect();
        rename(&scheme.ty, &fresh)
    }
}

fn rename(ty: &Type, map: &[(TyVar, Type)]) -> Type {
    match ty {
        Type::Var(v) => match map.iter().find(|(w, _)| w == v) {
            Some((_, replacement)) => replacement.clone(),
            None => ty.clone(),
        },
        Type::Con(con, args) => {
            Type::Con(*con, args.iter().map(|a| rename(a, map)).collect())
        }
    }
}
// ANCHOR_END: generalize

impl Infer<'_> {
    /// Infers the type of a closed program and generalizes it.
    pub fn run(&mut self, expr: &Expr) -> Result<Scheme, Diagnostic> {
        let ty = self.infer(expr)?;
        let (scheme, _) = self.generalize(&ty);
        if let Some(trace) = &mut self.trace {
            trace.push(format!(
                "{:<16} result {}",
                "(program)",
                scheme_raw(&scheme)
            ));
        }
        Ok(scheme)
    }

    // ANCHOR: infer
    // ANCHOR: infer_head
    fn infer(&mut self, expr: &Expr) -> Result<Type, Diagnostic> {
        match &expr.kind {
            ExprKind::Int(_) => Ok(Type::int()),
            ExprKind::Bool(_) => Ok(Type::bool()),
            // ANCHOR_END: infer_head
            // ANCHOR: infer_var
            // Rule Var: look the name up and instantiate its scheme.
            ExprKind::Var(name) => {
                let Some(binding) = self.env.iter().rev().find(|b| &b.name == name)
                else {
                    return Err(Diagnostic::error(format!(
                        "unbound variable `{name}`"
                    ))
                    .primary(expr.span, "not found in this scope"));
                };
                let scheme = binding.scheme.clone();
                let ty = self.instantiate(&scheme);
                if !scheme.vars.is_empty() {
                    self.log(
                        expr,
                        format!("instantiate {} as {ty}", scheme_raw(&scheme)),
                    );
                }
                Ok(ty)
            }
            // ANCHOR_END: infer_var
            // ANCHOR: infer_lam
            // Rule Abs: the parameter gets a fresh, monomorphic type.
            ExprKind::Lam(param, body) => {
                let alpha = Type::Var(self.subst.fresh());
                self.log(expr, format!("{param} : {alpha}"));
                self.bind(param, Scheme::mono(alpha.clone()), Origin::Lambda);
                let body_ty = self.infer(body);
                self.env.pop();
                Ok(Type::fun(alpha, body_ty?))
            }
            // ANCHOR_END: infer_lam
            // ANCHOR: infer_app
            // Rule App: the function's type must unify with arg -> result.
            ExprKind::App(func, arg) => {
                let func_ty = self.infer(func)?;
                let arg_ty = self.infer(arg)?;
                let result = Type::Var(self.subst.fresh());
                let wanted = Type::fun(arg_ty.clone(), result.clone());
                let before = (self.subst.apply(&func_ty), self.subst.apply(&arg_ty));
                let wanted_now = self.subst.apply(&wanted);
                let outcome = self.subst.unify(&func_ty, &wanted);
                self.log_unify(expr, &before.0, &wanted_now);
                match outcome {
                    Ok(()) => Ok(result),
                    Err(err) => {
                        Err(self.application_error(expr, func, arg, before, err))
                    }
                }
            }
            // ANCHOR_END: infer_app
            // ANCHOR: infer_let
            // Rule Let: infer, generalize, then check the body.
            ExprKind::Let(name, bound, body) => {
                let bound_ty = self.infer(bound)?;
                let (scheme, blocked) = self.generalize(&bound_ty);
                self.log(expr, format!("generalize {name} : {}", scheme_raw(&scheme)));
                self.bind(name, scheme, Origin::Let { blocked });
                let body_ty = self.infer(body);
                self.env.pop();
                body_ty
            }
            // ANCHOR_END: infer_let
            // ANCHOR: infer_letrec
            // Recursion: inside its definition the function is monomorphic.
            ExprKind::LetRec(name, bound, body) => {
                let alpha = Type::Var(self.subst.fresh());
                self.bind(name, Scheme::mono(alpha.clone()), Origin::Recursive);
                let bound_ty = self.infer(bound);
                self.env.pop();
                let bound_ty = bound_ty?;
                self.unify_or(expr, &alpha, &bound_ty, || {
                    Diagnostic::error("recursive function used at an inconsistent type")
                        .primary(bound.span, "in this definition")
                })?;
                let (scheme, blocked) = self.generalize(&bound_ty);
                self.log(expr, format!("generalize {name} : {}", scheme_raw(&scheme)));
                self.bind(name, scheme, Origin::Let { blocked });
                let body_ty = self.infer(body);
                self.env.pop();
                body_ty
            }
            // ANCHOR_END: infer_letrec
            // ANCHOR: infer_if
            // Rule If: a Bool condition and two branches of one type.
            ExprKind::If(cond, then_branch, else_branch) => {
                let cond_ty = self.infer(cond)?;
                let found = Namer::new().show(&self.subst.apply(&cond_ty));
                self.unify_or(expr, &cond_ty, &Type::bool(), || {
                    Diagnostic::error("mismatched types")
                        .primary(cond.span, format!("expected `Bool`, found `{found}`"))
                        .note("the condition of an `if` must be a `Bool`")
                })?;
                let then_ty = self.infer(then_branch)?;
                let else_ty = self.infer(else_branch)?;
                let mut namer = Namer::new();
                let expected = namer.show(&self.subst.apply(&then_ty));
                let found = namer.show(&self.subst.apply(&else_ty));
                self.unify_or(expr, &then_ty, &else_ty, || {
                    Diagnostic::error("`if` and `else` have incompatible types")
                        .primary(
                            else_branch.span,
                            format!("expected `{expected}`, found `{found}`"),
                        )
                        .secondary(then_branch.span, "expected because of this")
                })?;
                Ok(then_ty)
            }
            // ANCHOR_END: infer_if
            ExprKind::Pair(first, second) => {
                let first_ty = self.infer(first)?;
                let second_ty = self.infer(second)?;
                Ok(Type::pair(first_ty, second_ty))
            }
        }
    }
    // ANCHOR_END: infer

    fn bind(&mut self, name: &str, scheme: Scheme, origin: Origin) {
        self.env.push(Binding {
            name: name.to_string(),
            scheme,
            origin,
        });
    }

    /// Unifies two types; on failure, returns the diagnostic built by `error`.
    fn unify_or(
        &mut self,
        expr: &Expr,
        left: &Type,
        right: &Type,
        error: impl FnOnce() -> Diagnostic,
    ) -> Result<(), Diagnostic> {
        let shown = (self.subst.apply(left), self.subst.apply(right));
        let result = self.subst.unify(left, right);
        self.log_unify(expr, &shown.0, &shown.1);
        result.map_err(|_| error())
    }
}

// ANCHOR: errors
impl Infer<'_> {
    /// Explains why `func arg` is ill-typed. `before` holds the types of the
    /// function and the argument as they were just before unification.
    fn application_error(
        &self,
        app: &Expr,
        func: &Expr,
        arg: &Expr,
        before: (Type, Type),
        err: UnifyError,
    ) -> Diagnostic {
        let (func_ty, arg_ty) = before;
        let mut namer = Namer::new();
        let func_text = func.text(self.source);
        let arg_text = arg.text(self.source);
        match (err, &func_ty) {
            (UnifyError::Occurs(v, ty), _) => {
                let (var, ty) = (namer.show(&Type::Var(v)), namer.show(&ty));
                let (f_ty, a_ty) = (namer.show(&func_ty), namer.show(&arg_ty));
                Diagnostic::error(format!(
                    "infinite type: `{var}` would have to equal `{ty}`"
                ))
                .primary(app.span, "in this application")
                .note(format!("the function `{func_text}` has type `{f_ty}`"))
                .note(format!("its argument `{arg_text}` has type `{a_ty}`"))
                .note(format!(
                    "no finite type satisfies `{var} = {ty}` (the occurs check)"
                ))
            }
            (UnifyError::Mismatch(..), Type::Con(TyCon::Fun, params)) => {
                let expected = namer.show(&params[0]);
                let found = namer.show(&arg_ty);
                let whole = namer.show(&func_ty);
                let diag = Diagnostic::error("mismatched types")
                    .primary(
                        arg.span,
                        format!("expected `{expected}`, found `{found}`"),
                    )
                    .secondary(func.span, format!("this function has type `{whole}`"));
                self.explain_binding(diag, func)
            }
            (UnifyError::Mismatch(..), _) => {
                let ty = namer.show(&func_ty);
                Diagnostic::error(format!("`{func_text}` is not a function"))
                    .primary(func.span, format!("this has type `{ty}`"))
                    .secondary(arg.span, "but it is applied to this argument")
            }
        }
    }

    // ANCHOR: explain_binding
    /// When the function is a variable, says how it was bound: this is what
    /// decides whether it may be used at several types.
    fn explain_binding(&self, diag: Diagnostic, func: &Expr) -> Diagnostic {
        let ExprKind::Var(name) = &func.kind else {
            return diag;
        };
        let Some(binding) = self.env.iter().rev().find(|b| &b.name == name) else {
            return diag;
        };
        match binding.origin {
            Origin::Lambda => diag
                .note(format!(
                    "`{name}` is a parameter of `fun`, so all its uses share one type"
                ))
                .help(format!("bind `{name}` with `let` to make it polymorphic")),
            Origin::Let { blocked: true } => diag.note(format!(
                "`{name}` was not generalized: its type variables occur in the \
                 environment"
            )),
            Origin::Recursive => diag.note(format!(
                "`{name}` is used in its own definition, where it is not yet \
                 polymorphic"
            )),
            Origin::Prelude | Origin::Let { blocked: false } => diag,
        }
    }
    // ANCHOR_END: explain_binding
}
// ANCHOR_END: errors

// Tracing: one line per step, the source text on the left.
impl Infer<'_> {
    fn log(&mut self, expr: &Expr, event: String) {
        if self.trace.is_none() {
            return;
        }
        let text = short(expr, self.source);
        if let Some(trace) = &mut self.trace {
            trace.push(format!("{text:<16} {event}"));
        }
    }

    /// Logs a unification, given the two sides as they were before it, and
    /// the variables it solved.
    fn log_unify(&mut self, expr: &Expr, left: &Type, right: &Type) {
        let steps = self.subst.take_trace();
        if self.trace.is_none() {
            return;
        }
        let solved: Vec<String> = steps
            .iter()
            .filter(|s| s.contains(":="))
            .map(|s| s.trim().to_string())
            .collect();
        let mut event = format!("unify {left} ~ {right}");
        if !solved.is_empty() {
            event += &format!("  =>  {}", solved.join(", "));
        }
        self.log(expr, event);
    }
}

/// The source text of an expression, abbreviated for the trace.
fn short(expr: &Expr, source: &str) -> String {
    match &expr.kind {
        ExprKind::Lam(param, _) => format!("fun {param} -> .."),
        ExprKind::Let(name, _, _) => format!("let {name} = .."),
        ExprKind::LetRec(name, _, _) => format!("let rec {name} = .."),
        _ => {
            let text = expr
                .text(source)
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ");
            if text.chars().count() > 16 {
                format!("{}..", text.chars().take(14).collect::<String>())
            } else {
                text
            }
        }
    }
}

/// A scheme for the trace: bound variables get letters, free (inference)
/// variables keep their `?n` form, as in `forall a. a -> ?3`.
fn scheme_raw(scheme: &Scheme) -> String {
    if scheme.vars.is_empty() {
        return scheme.ty.to_string();
    }
    let mut namer = Namer::new();
    let mut name = |v: TyVar| {
        if scheme.vars.contains(&v) {
            namer.name(v)
        } else {
            format!("?{}", v.0)
        }
    };
    let body = show_with(&scheme.ty, &mut name);
    let bound: Vec<String> = scheme
        .ty
        .vars()
        .into_iter()
        .filter(|v| scheme.vars.contains(v))
        .map(|v| namer.name(v))
        .collect();
    format!("forall {}. {body}", bound.join(" "))
}

/// Renumbers the inference variables of a trace as `?0`, `?1`, ... in order
/// of first appearance. (The prelude's schemes use up the first variables,
/// which would otherwise make the numbers of a short program start high.)
fn renumber(trace: Vec<String>) -> Vec<String> {
    let mut seen: Vec<String> = Vec::new();
    trace
        .into_iter()
        .map(|line| {
            let mut out = String::new();
            let mut chars = line.chars().peekable();
            while let Some(c) = chars.next() {
                out.push(c);
                if c != '?' {
                    continue;
                }
                let mut digits = String::new();
                while let Some(d) = chars.peek().filter(|d| d.is_ascii_digit()) {
                    digits.push(*d);
                    chars.next();
                }
                if !digits.is_empty() {
                    let index = match seen.iter().position(|s| *s == digits) {
                        Some(i) => i,
                        None => {
                            seen.push(digits);
                            seen.len() - 1
                        }
                    };
                    out += &index.to_string();
                }
            }
            out
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::principal_type;

    fn ok(src: &str) -> String {
        principal_type(src)
            .unwrap_or_else(|e| panic!("{src} should be well typed:\n{e}"))
    }

    fn headline(src: &str) -> String {
        let err = principal_type(src).expect_err("should be ill-typed");
        err.lines().next().unwrap().to_string()
    }

    #[test]
    fn principal_types_of_combinators() {
        assert_eq!(ok("fun x -> x"), "forall a. a -> a");
        assert_eq!(ok("fun x y -> x"), "forall a b. a -> b -> a");
        assert_eq!(ok("fun f x -> f (f x)"), "forall a. (a -> a) -> a -> a");
        assert_eq!(
            ok("fun f g x -> f (g x)"),
            "forall a b c. (a -> b) -> (c -> a) -> c -> b"
        );
        assert_eq!(
            ok("fun f g x -> f x (g x)"),
            "forall a b c. (a -> b -> c) -> (a -> b) -> a -> c"
        );
    }

    #[test]
    fn literals_operators_and_prelude() {
        assert_eq!(ok("1 + 2 * 3"), "Int");
        assert_eq!(ok("fun x -> x < 3"), "Int -> Bool");
        assert_eq!(ok("fun p -> (snd p, fst p)"), "forall a b. a * b -> b * a");
        assert_eq!(ok("[1, 2, 3]"), "List Int");
        assert_eq!(ok("[]"), "forall a. List a");
        assert_eq!(ok("fun x xs -> x :: xs"), "forall a. a -> List a -> List a");
    }

    #[test]
    fn recursion() {
        let map = "let rec map f xs = \
                   if null xs then [] else f (head xs) :: map f (tail xs) in map";
        assert_eq!(ok(map), "forall a b. (a -> b) -> List a -> List b");
        let length =
            "let rec length xs = if null xs then 0 else 1 + length (tail xs) in length";
        assert_eq!(ok(length), "forall a. List a -> Int");
    }

    #[test]
    fn let_is_polymorphic_but_fun_is_not() {
        assert_eq!(ok("let id = fun x -> x in (id 1, id true)"), "Int * Bool");
        assert_eq!(
            headline("(fun id -> (id 1, id true)) (fun x -> x)"),
            "error: mismatched types"
        );
        // The same `fun` is fine when its parameter is used at one type only.
        assert_eq!(ok("(fun id -> (id 1, id 2)) (fun x -> x)"), "Int * Int");
    }

    #[test]
    fn generalization_respects_the_environment() {
        // y's type is x's type, which is free in the environment: no generalization.
        assert_eq!(
            headline("fun x -> let y = x in (y 1, y true)"),
            "error: mismatched types"
        );
        // Here nothing is shared with the environment, so `k` is polymorphic.
        assert_eq!(
            ok("fun x -> let k = fun y -> x in (k 1, k true)"),
            "forall a. a -> a * a"
        );
    }

    #[test]
    fn the_occurs_check_rejects_self_application() {
        let err = principal_type("fun x -> x x").unwrap_err();
        assert!(
            err.starts_with("error: infinite type: `a` would have to equal `a -> b`")
        );
        assert!(err.contains("(the occurs check)"));
    }

    #[test]
    fn other_errors() {
        assert_eq!(headline("y"), "error: unbound variable `y`");
        assert_eq!(headline("1 2"), "error: `1` is not a function");
        assert_eq!(headline("if 1 then 2 else 3"), "error: mismatched types");
        assert_eq!(
            headline("if true then 1 else false"),
            "error: `if` and `else` have incompatible types"
        );
        assert_eq!(
            headline("let rec f x = if true then 0 else f 1 + f true in f"),
            "error: mismatched types"
        );
        assert_eq!(
            headline("fun x -> x +"),
            "error: expected an expression, found the end of the program"
        );
    }

    #[test]
    fn errors_explain_how_the_function_was_bound() {
        let err =
            principal_type("(fun id -> (id 1, id true)) (fun x -> x)").unwrap_err();
        assert!(err.contains("`id` is a parameter of `fun`"));
        let err = principal_type("let rec f x = if true then 0 else f 1 + f true in f")
            .unwrap_err();
        assert!(err.contains("in its own definition"));
    }

    #[test]
    fn trace_is_renumbered_from_zero() {
        let (trace, result) = crate::trace_program("fun x -> x");
        assert!(result.is_ok());
        assert_eq!(
            trace[0].split_whitespace().collect::<Vec<_>>(),
            ["fun", "x", "->", "..", "x", ":", "?0"]
        );
    }
}
