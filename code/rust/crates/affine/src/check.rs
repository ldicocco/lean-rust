//! The checker: λ^aff with input and output contexts.
//!
//! The declarative rules of Chapter 22 split the context Γ = Γ₁ ⊎ Γ₂ between
//! the subterms, and they leave it to us to guess the split. The checker does
//! not guess. It gives the *whole* context to the first subterm, takes back
//! what is left over, and gives that to the second subterm. A variable that the
//! first subterm consumed is marked as moved in the leftovers, so a second use
//! is caught: that is error E0382.
//!
//! On top of the calculus, the checker tracks moves per *place* (`p.0`,
//! `r.sensor`), as rustc does, so that it can accept partial moves.

use crate::copy::{Discipline, check_derives, is_clone, is_copy};
use crate::derivation::Derivation;
use crate::diagnostic::{Diagnostic, Label};
use crate::syntax::*;

// ANCHOR: binding
/// One variable in the context, with everything the checker knows about it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    pub name: String,
    pub ty: Ty,
    /// Where the variable was introduced (a parameter or a `let`).
    pub decl: Span,
    /// How many closures enclose the place where the variable was introduced.
    pub depth: usize,
    /// The moves out of this variable or out of parts of it. No moves: the
    /// variable is available. A move with an empty path: it is gone.
    pub moves: Vec<Move>,
    /// How many times the variable was used (moved, copied or cloned).
    pub uses: usize,
}

/// A move out of a place `x.path`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Move {
    pub path: Vec<Proj>,
    pub span: Span,
    pub kind: MoveKind,
}

/// How a move happened, for the labels of error messages.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MoveKind {
    /// An ordinary use by value: "value moved here".
    Plain,
    /// A use inside a closure body: the closure captured the variable.
    IntoClosure { use_span: Span },
    /// Calling a closure consumes it: "`f` moved due to this call".
    Call,
}

/// The typing context: a stack of bindings, innermost last. Shadowing is
/// allowed, as in Rust: a name refers to its innermost binding.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Ctx {
    pub bindings: Vec<Binding>,
}
// ANCHOR_END: binding

impl Ctx {
    fn lookup(&self, name: &str) -> Option<usize> {
        self.bindings.iter().rposition(|b| b.name == name)
    }

    fn push(&mut self, name: &Ident, ty: Ty, depth: usize) {
        self.bindings.push(Binding {
            name: name.name.clone(),
            ty,
            decl: name.span,
            depth,
            moves: Vec::new(),
            uses: 0,
        });
    }

    fn uses_snapshot(&self) -> Vec<usize> {
        self.bindings.iter().map(|b| b.uses).collect()
    }

    /// The variables used since the snapshot `before` was taken.
    fn used_since(&self, before: &[usize]) -> Vec<(String, Ty)> {
        self.bindings
            .iter()
            .zip(before)
            .filter(|(b, n)| b.uses > **n)
            .map(|(b, _)| (b.name.clone(), b.ty.clone()))
            .collect()
    }
}

// ANCHOR: merge
/// The leftovers of two alternatives that started from the same context (the
/// two components of `with(a, b)`, the two arms of a `match`): a variable is
/// moved afterwards if *either* alternative moved it.
fn merge(mut a: Ctx, b: Ctx) -> Ctx {
    for (x, y) in a.bindings.iter_mut().zip(b.bindings) {
        for m in y.moves {
            if !x.moves.contains(&m) {
                x.moves.push(m);
            }
        }
        x.uses = x.uses.max(y.uses);
    }
    a
}
// ANCHOR_END: merge

/// The result of checking an expression: its type, the leftover context and
/// the derivation.
pub struct Checked {
    pub ty: Ty,
    pub ctx: Ctx,
    pub deriv: Derivation,
}

/// The outcome of checking one function.
#[derive(Clone, Debug)]
pub struct FnReport {
    pub name: String,
    /// The signature, for printing: `fn swap(p: (String, File)) -> (File, String)`.
    pub signature: String,
    pub derivation: Derivation,
    /// Parameters (or parts of them) still owned at the end of the body: they
    /// are discarded, by weakening (and, in Rust, dropped).
    pub dropped: Vec<String>,
}

/// The outcome of checking a program: the functions that check, and the
/// errors, in the order of the items.
#[derive(Clone, Debug, Default)]
pub struct Report {
    pub functions: Vec<FnReport>,
    pub errors: Vec<Diagnostic>,
}

/// Check every item of a program.
pub fn check_program(program: &Program, discipline: Discipline) -> Report {
    let mut report = Report::default();
    for item in &program.items {
        match item {
            Item::Struct(s) if discipline == Discipline::Copy => {
                report.errors.extend(check_derives(program, s));
            }
            Item::Fn(f) => {
                if let Some(body) = &f.body {
                    let mut checker = Checker {
                        program,
                        discipline,
                        closures: Vec::new(),
                        discarded: Vec::new(),
                    };
                    match checker.check_fn(f, body) {
                        Ok(r) => report.functions.push(r),
                        Err(d) => report.errors.push(d),
                    }
                }
            }
            _ => {}
        }
    }
    report
}

/// The checker for one function body.
pub struct Checker<'p> {
    program: &'p Program,
    discipline: Discipline,
    /// The heads `|x: T|` of the closures around the expression being checked.
    closures: Vec<Span>,
    /// Variables that went out of scope while still owning something.
    discarded: Vec<String>,
}

fn signature(f: &FnDef) -> String {
    let params: Vec<String> = f
        .params
        .iter()
        .map(|(x, t)| format!("{}: {t}", x.name))
        .collect();
    format!("fn {}({}) -> {}", f.name.name, params.join(", "), f.ret)
}

fn place_name(name: &str, path: &[Proj]) -> String {
    let mut s = name.to_string();
    for p in path {
        s += &p.to_string();
    }
    s
}

/// If `e` is a place `x.p1.p2...`, its root variable and path.
fn as_place(e: &Expr) -> Option<(Ident, Vec<Proj>)> {
    match &e.kind {
        ExprKind::Var(x) => Some((
            Ident {
                name: x.clone(),
                span: e.span,
            },
            Vec::new(),
        )),
        ExprKind::Field(base, proj, _) => {
            let (root, mut path) = as_place(base)?;
            path.push(proj.clone());
            Some((root, path))
        }
        _ => None,
    }
}

impl Checker<'_> {
    fn is_copy(&self, ty: &Ty) -> bool {
        self.discipline == Discipline::Copy && is_copy(self.program, ty)
    }

    fn is_clone(&self, ty: &Ty) -> bool {
        self.discipline == Discipline::Copy && is_clone(self.program, ty)
    }

    fn check_fn(&mut self, f: &FnDef, body: &Expr) -> Result<FnReport, Diagnostic> {
        let mut ctx = Ctx::default();
        for (x, t) in &f.params {
            ctx.push(x, t.clone(), 0);
        }
        let mut checked = self.infer(ctx, body, Some(&f.ret))?;
        // Whatever the parameters still own at the end of the body is
        // discarded, like the local variables that went out of scope before.
        while !checked.ctx.bindings.is_empty() {
            self.pop_scope(&mut checked.ctx);
        }
        Ok(FnReport {
            name: f.name.name.clone(),
            signature: signature(f),
            derivation: checked.deriv,
            dropped: std::mem::take(&mut self.discarded),
        })
    }

    /// A variable goes out of scope. If it still owns something, that is
    /// discarded (weakening; in Rust, a drop): remember it for the report.
    fn pop_scope(&mut self, ctx: &mut Ctx) {
        let Some(b) = ctx.bindings.pop() else { return };
        // Discarding a Copy value, or a (), is free: there is nothing to drop.
        if self.is_copy(&b.ty) || b.ty == Ty::Unit {
            return;
        }
        if b.moves.is_empty() {
            self.discarded.push(b.name);
        } else if b.moves.iter().all(|m| !m.path.is_empty()) {
            self.discarded.push(format!("the rest of {}", b.name));
        }
    }

    // ANCHOR: infer
    /// Check `e` in the context `ctx`, which it consumes; return the type, the
    /// leftover context and the derivation. `expected` is the type that the
    /// surrounding code expects, if it is known.
    pub fn infer(
        &mut self,
        ctx: Ctx,
        e: &Expr,
        expected: Option<&Ty>,
    ) -> Result<Checked, Diagnostic> {
        let before = ctx.uses_snapshot();
        let (ty, ctx, rule, premises) = self.infer_kind(ctx, e, expected)?;
        if let Some(want) = expected {
            if *want != ty {
                return Err(mismatch(e.span, want, &ty));
            }
        }
        let deriv = Derivation {
            rule,
            ctx: ctx.used_since(&before),
            expr: show_expr_brief(e),
            ty: ty.clone(),
            premises,
        };
        Ok(Checked { ty, ctx, deriv })
    }
    // ANCHOR_END: infer

    fn infer_kind(
        &mut self,
        ctx: Ctx,
        e: &Expr,
        expected: Option<&Ty>,
    ) -> Result<(Ty, Ctx, &'static str, Vec<Derivation>), Diagnostic> {
        match &e.kind {
            ExprKind::Var(_) | ExprKind::Field(..) => self.infer_projection(ctx, e),
            ExprKind::Unit => Ok((Ty::Unit, ctx, "A-Unit", vec![])),
            ExprKind::Int(_) => Ok((Ty::named("i32"), ctx, "Lit", vec![])),
            // ANCHOR: pair
            ExprKind::Tuple(a, b) => {
                let (ea, eb) = match expected {
                    Some(Ty::Tuple(x, y)) => (Some(&**x), Some(&**y)),
                    _ => (None, None),
                };
                // The first component gets the whole context; the second gets
                // what the first one left over.
                let first = self.infer(ctx, a, ea)?;
                let second = self.infer(first.ctx, b, eb)?;
                let ty = Ty::tuple(first.ty, second.ty);
                Ok((ty, second.ctx, "A-Pair", vec![first.deriv, second.deriv]))
            }
            // ANCHOR_END: pair
            ExprKind::Let {
                pat,
                ty,
                value,
                body,
            } => self.infer_let(ctx, pat, ty.as_ref(), value, body, expected),
            ExprKind::Closure {
                param,
                ty,
                body,
                head,
                ..
            } => {
                let want = match expected {
                    Some(Ty::Fn(_, b)) => Some((**b).clone()),
                    _ => None,
                };
                self.closures.push(*head);
                let mut inner = ctx;
                inner.push(param, ty.clone(), self.closures.len());
                let result = self.infer(inner, body, want.as_ref());
                self.closures.pop();
                let mut body = result?;
                self.pop_scope(&mut body.ctx);
                with_binders(&mut body.deriv, &[(param, ty)]);
                let fn_ty = Ty::func(ty.clone(), body.ty);
                Ok((fn_ty, body.ctx, "A-Abs", vec![body.deriv]))
            }
            ExprKind::Call { callee, args } => self.infer_call(ctx, e, callee, args),
            // ANCHOR: with
            ExprKind::With(a, b) => {
                let (ea, eb) = match expected {
                    Some(Ty::With(x, y)) => (Some(&**x), Some(&**y)),
                    _ => (None, None),
                };
                // Both alternatives start from the same context: the only
                // place where the checker copies a context is where the
                // rules share one.
                let left = self.infer(ctx.clone(), a, ea)?;
                let right = self.infer(ctx, b, eb)?;
                let ty = Ty::With(Box::new(left.ty), Box::new(right.ty));
                let out = merge(left.ctx, right.ctx);
                Ok((ty, out, "A-With", vec![left.deriv, right.deriv]))
            }
            // ANCHOR_END: with
            ExprKind::Left(a) | ExprKind::Right(a) => {
                let is_left = matches!(e.kind, ExprKind::Left(_));
                let Some(Ty::Either(l, r)) = expected else {
                    return Err(Diagnostic::new("E0282", "type annotations needed")
                        .with(Label::primary(e.span, "cannot infer the type of this `Either`"))
                        .note("help: give the variable a type, as in `let x: Either<A, B> = ...`"));
                };
                let want = if is_left { &**l } else { &**r };
                let inner = self.infer(ctx, a, Some(want))?;
                let rule = if is_left { "A-Inl" } else { "A-Inr" };
                let ty = Ty::Either(l.clone(), r.clone());
                Ok((ty, inner.ctx, rule, vec![inner.deriv]))
            }
            ExprKind::Match {
                scrutinee,
                left,
                right,
            } => self.infer_match(ctx, scrutinee, left, right, expected),
            ExprKind::Clone(base) => self.infer_clone(ctx, e, base),
            ExprKind::StructLit { name, fields } => {
                self.infer_struct(ctx, e, name, fields)
            }
        }
    }

    fn infer_let(
        &mut self,
        ctx: Ctx,
        pat: &Pat,
        ann: Option<&Ty>,
        value: &Expr,
        body: &Expr,
        expected: Option<&Ty>,
    ) -> Result<(Ty, Ctx, &'static str, Vec<Derivation>), Diagnostic> {
        let first = self.infer(ctx, value, ann)?;
        let depth = self.closures.len();
        let mut inner = first.ctx;
        let binders: Vec<(Ident, Ty)> = match pat {
            Pat::Wild => vec![],
            Pat::Var(x) => vec![(x.clone(), first.ty.clone())],
            Pat::Pair(x, y) => match &first.ty {
                Ty::Tuple(a, b) => {
                    vec![(x.clone(), (**a).clone()), (y.clone(), (**b).clone())]
                }
                other => {
                    return Err(Diagnostic::new("E0308", "mismatched types").with(
                        Label::primary(
                            value.span,
                            &format!("expected a tuple, found `{other}`"),
                        ),
                    ));
                }
            },
        };
        for (x, t) in &binders {
            inner.push(x, t.clone(), depth);
        }
        let mut second = self.infer(inner, body, expected)?;
        for _ in &binders {
            self.pop_scope(&mut second.ctx);
        }
        let refs: Vec<(&Ident, &Ty)> = binders.iter().map(|(x, t)| (x, t)).collect();
        with_binders(&mut second.deriv, &refs);
        let rule = if matches!(pat, Pat::Pair(..)) {
            "A-LetPair"
        } else {
            "A-Let"
        };
        Ok((second.ty, second.ctx, rule, vec![first.deriv, second.deriv]))
    }

    fn infer_match(
        &mut self,
        ctx: Ctx,
        scrutinee: &Expr,
        left: &(Ident, Box<Expr>),
        right: &(Ident, Box<Expr>),
        expected: Option<&Ty>,
    ) -> Result<(Ty, Ctx, &'static str, Vec<Derivation>), Diagnostic> {
        let scrut = self.infer(ctx, scrutinee, None)?;
        let Ty::Either(l, r) = &scrut.ty else {
            return Err(Diagnostic::new("E0308", "mismatched types").with(
                Label::primary(
                    scrutinee.span,
                    &format!("expected an `Either`, found `{}`", scrut.ty),
                ),
            ));
        };
        let depth = self.closures.len();
        // Both arms start from the leftovers of the scrutinee.
        let mut ctx_l = scrut.ctx.clone();
        ctx_l.push(&left.0, (**l).clone(), depth);
        let mut arm_l = self.infer(ctx_l, &left.1, expected)?;
        self.pop_scope(&mut arm_l.ctx);
        with_binders(&mut arm_l.deriv, &[(&left.0, l)]);
        let mut ctx_r = scrut.ctx;
        ctx_r.push(&right.0, (**r).clone(), depth);
        let want = expected.cloned().unwrap_or(arm_l.ty.clone());
        let mut arm_r = self.infer(ctx_r, &right.1, Some(&want)).map_err(|d| {
            if d.code.as_deref() == Some("E0308") && expected.is_none() {
                Diagnostic::new("E0308", "`match` arms have incompatible types")
                    .with(Label::secondary(left.1.span, "this is found to be of type"))
                    .with(Label::primary(right.1.span, &format!("expected `{want}`")))
            } else {
                d
            }
        })?;
        self.pop_scope(&mut arm_r.ctx);
        with_binders(&mut arm_r.deriv, &[(&right.0, r)]);
        let out = merge(arm_l.ctx, arm_r.ctx);
        Ok((
            arm_l.ty,
            out,
            "A-Case",
            vec![scrut.deriv, arm_l.deriv, arm_r.deriv],
        ))
    }

    fn infer_call(
        &mut self,
        ctx: Ctx,
        e: &Expr,
        callee: &Ident,
        args: &[Expr],
    ) -> Result<(Ty, Ctx, &'static str, Vec<Derivation>), Diagnostic> {
        // A closure in scope: calling it consumes it (it is FnOnce).
        if let Some(i) = ctx.lookup(&callee.name) {
            let fn_ty = ctx.bindings[i].ty.clone();
            let Ty::Fn(param, ret) = &fn_ty else {
                return Err(Diagnostic::new(
                    "E0618",
                    &format!("expected function, found `{fn_ty}`"),
                )
                .with(Label::secondary(
                    ctx.bindings[i].decl,
                    &format!("`{}` has type `{fn_ty}`", callee.name),
                ))
                .with(Label::primary(e.span, "call expression requires function")));
            };
            if args.len() != 1 {
                return Err(arity(e.span, 1, args.len()));
            }
            let before = ctx.uses_snapshot();
            let (_, ctx) = self.use_place(
                ctx,
                callee,
                &[],
                callee.span,
                (e.span, MoveKind::Call),
            )?;
            let f_deriv = Derivation {
                rule: "A-Var",
                ctx: ctx.used_since(&before),
                expr: callee.name.clone(),
                ty: fn_ty.clone(),
                premises: vec![],
            };
            let arg = self.infer(ctx, &args[0], Some(param))?;
            return Ok(((**ret).clone(), arg.ctx, "A-App", vec![f_deriv, arg.deriv]));
        }
        // A declared function is a constant: calling it uses nothing but its
        // arguments, which are checked from left to right.
        let (params, ret): (Vec<Ty>, Ty) = match self.program.function(&callee.name) {
            Some(f) => (
                f.params.iter().map(|(_, t)| t.clone()).collect(),
                f.ret.clone(),
            ),
            None if callee.name == "drop" && args.len() == 1 => {
                // `drop` is λx. (): it consumes its argument and returns ().
                let arg = self.infer(ctx, &args[0], None)?;
                return Ok((Ty::Unit, arg.ctx, "Call", vec![arg.deriv]));
            }
            None => {
                return Err(Diagnostic::new(
                    "E0425",
                    &format!("cannot find function `{}` in this scope", callee.name),
                )
                .with(Label::primary(callee.span, "not found in this scope")));
            }
        };
        if params.len() != args.len() {
            return Err(arity(e.span, params.len(), args.len()));
        }
        let mut ctx = ctx;
        let mut premises = Vec::new();
        for (arg, param) in args.iter().zip(&params) {
            let checked = self.infer(ctx, arg, Some(param))?;
            ctx = checked.ctx;
            premises.push(checked.deriv);
        }
        Ok((ret, ctx, "Call", premises))
    }

    /// `x`, `x.0`, `r.sensor`, `w.fst`, `f().0`, ...
    fn infer_projection(
        &mut self,
        ctx: Ctx,
        e: &Expr,
    ) -> Result<(Ty, Ctx, &'static str, Vec<Derivation>), Diagnostic> {
        if let Some((root, path)) = as_place(e) {
            // The longest prefix of the path that is a place (tuple fields and
            // struct fields); what follows (`.fst`, `.snd` of a `With`) is
            // applied to the value.
            let Some(i) = ctx.lookup(&root.name) else {
                return Err(Diagnostic::new(
                    "E0425",
                    &format!("cannot find value `{}` in this scope", root.name),
                )
                .with(Label::primary(root.span, "not found in this scope")));
            };
            let mut ty = ctx.bindings[i].ty.clone();
            let mut k = 0;
            while k < path.len() {
                match self.place_step(&ty, &path[k]) {
                    Some(next) => {
                        ty = next;
                        k += 1;
                    }
                    None => break,
                }
            }
            let (ty, ctx) = self.use_place(
                ctx,
                &root,
                &path[..k],
                e.span,
                (e.span, MoveKind::Plain),
            )?;
            let ty = self.value_projections(ty, &path[k..], e.span)?;
            let rule = if path.is_empty() {
                "A-Var"
            } else if k == path.len() {
                "Place"
            } else {
                "A-Proj"
            };
            return Ok((ty, ctx, rule, vec![]));
        }
        let ExprKind::Field(base, proj, _) = &e.kind else {
            unreachable!("as_place handles variables");
        };
        let inner = self.infer(ctx, base, None)?;
        let ty =
            self.value_projections(inner.ty, std::slice::from_ref(proj), e.span)?;
        Ok((ty, inner.ctx, "A-Proj", vec![inner.deriv]))
    }

    /// One step of a place: a field of a tuple or of a struct.
    fn place_step(&self, ty: &Ty, proj: &Proj) -> Option<Ty> {
        match (ty, proj) {
            (Ty::Tuple(a, _), Proj::Index(0)) => Some((**a).clone()),
            (Ty::Tuple(_, b), Proj::Index(1)) => Some((**b).clone()),
            (Ty::Named(n), Proj::Field(f)) => {
                let s = self.program.structure(n)?;
                s.fields
                    .iter()
                    .find(|(x, _, _)| x.name == *f)
                    .map(|(_, t, _)| t.clone())
            }
            _ => None,
        }
    }

    /// Projections applied to a value: `.fst` and `.snd` of a `With` choose one
    /// alternative; a field of a tuple or struct value keeps that field and
    /// discards the rest (weakening).
    fn value_projections(
        &self,
        mut ty: Ty,
        path: &[Proj],
        span: Span,
    ) -> Result<Ty, Diagnostic> {
        for proj in path {
            ty = match (&ty, proj) {
                (Ty::With(a, _), Proj::Field(f)) if f == "fst" => (**a).clone(),
                (Ty::With(_, b), Proj::Field(f)) if f == "snd" => (**b).clone(),
                _ => match self.place_step(&ty, proj) {
                    Some(t) => t,
                    None => {
                        return Err(Diagnostic::new(
                            "E0609",
                            &format!(
                                "no field `{}` on type `{ty}`",
                                &proj.to_string()[1..]
                            ),
                        )
                        .with(Label::primary(span, "unknown field")));
                    }
                },
            };
        }
        Ok(ty)
    }

    // ANCHOR: use_place
    /// Use the place `root.path` by value: move it, or copy it if its type is
    /// `Copy`. This is where E0382 comes from.
    fn use_place(
        &mut self,
        mut ctx: Ctx,
        root: &Ident,
        path: &[Proj],
        use_span: Span,
        (move_span, kind): (Span, MoveKind),
    ) -> Result<(Ty, Ctx), Diagnostic> {
        let i = ctx
            .lookup(&root.name)
            .expect("the caller looked the variable up");
        let b = &ctx.bindings[i];
        let mut ty = b.ty.clone();
        for p in path {
            ty = self
                .place_step(&ty, p)
                .expect("the caller checked the path");
        }
        // Moved before: this place, or a place that contains it.
        let moved: Vec<&Move> = b
            .moves
            .iter()
            .filter(|m| path.starts_with(&m.path))
            .collect();
        if !moved.is_empty() {
            return Err(self.use_after_move(b, &moved, path, use_span));
        }
        // A part of this place was moved before.
        let partly: Vec<&Move> = b
            .moves
            .iter()
            .filter(|m| m.path.starts_with(path))
            .collect();
        if !partly.is_empty() {
            return Err(self.use_after_partial_move(b, &partly, path, use_span));
        }
        let b = &mut ctx.bindings[i];
        b.uses += 1;
        if !self.is_copy(&ty) {
            // A variable from outside the innermost closures is captured.
            let (span, kind) = if b.depth < self.closures.len() {
                (self.closures[b.depth], MoveKind::IntoClosure { use_span })
            } else {
                (move_span, kind)
            };
            b.moves.push(Move {
                path: path.to_vec(),
                span,
                kind,
            });
        }
        Ok((ty, ctx))
    }
    // ANCHOR_END: use_place

    fn use_after_move(
        &self,
        b: &Binding,
        moved: &[&Move],
        path: &[Proj],
        use_span: Span,
    ) -> Diagnostic {
        let place = place_name(&b.name, path);
        let mut d = Diagnostic::new("E0382", &format!("use of moved value: `{place}`"));
        let whole = moved.iter().any(|m| m.path.is_empty());
        if whole {
            d = d.with(Label::secondary(
                b.decl,
                &format!(
                    "move occurs because `{}` has type `{}`, which does not implement the `Copy` trait",
                    b.name, b.ty
                ),
            ));
        }
        for m in moved {
            d = move_labels(d, m, &b.name);
        }
        d = d.with(Label::primary(use_span, "value used here after move"));
        for m in moved.iter().filter(|m| !m.path.is_empty()) {
            let ty = self.path_type(&b.ty, &m.path);
            d = d.note(&format!(
                "note: move occurs because `{}` has type `{ty}`, which does not implement the `Copy` trait",
                place_name(&b.name, &m.path)
            ));
        }
        if self.is_clone(&b.ty) && whole {
            d = d.note("help: consider cloning the value if the performance cost is acceptable");
        }
        d
    }

    fn use_after_partial_move(
        &self,
        b: &Binding,
        partly: &[&Move],
        path: &[Proj],
        use_span: Span,
    ) -> Diagnostic {
        let place = place_name(&b.name, path);
        let mut d = Diagnostic::new(
            "E0382",
            &format!("use of partially moved value: `{place}`"),
        );
        for m in partly {
            d = d.with(Label::secondary(m.span, "value partially moved here"));
        }
        d = d.with(Label::primary(
            use_span,
            "value used here after partial move",
        ));
        for m in partly {
            let ty = self.path_type(&b.ty, &m.path);
            d = d.note(&format!(
                "note: partial move occurs because `{}` has type `{ty}`, which does not implement the `Copy` trait",
                place_name(&b.name, &m.path)
            ));
        }
        d
    }

    fn path_type(&self, ty: &Ty, path: &[Proj]) -> Ty {
        let mut ty = ty.clone();
        for p in path {
            ty = self.place_step(&ty, p).unwrap_or(ty);
        }
        ty
    }

    /// `place.clone()`: a read of the place (in Rust, through a shared borrow)
    /// that produces a new value. It does not move the place.
    fn infer_clone(
        &mut self,
        mut ctx: Ctx,
        e: &Expr,
        base: &Expr,
    ) -> Result<(Ty, Ctx, &'static str, Vec<Derivation>), Diagnostic> {
        let Some((root, path)) = as_place(base) else {
            return Err(Diagnostic::new(
                "E0599",
                "`.clone()` can only be applied to a variable or a field",
            )
            .with(Label::primary(e.span, "not a place")));
        };
        let Some(i) = ctx.lookup(&root.name) else {
            return Err(Diagnostic::new(
                "E0425",
                &format!("cannot find value `{}` in this scope", root.name),
            )
            .with(Label::primary(root.span, "not found in this scope")));
        };
        let b = &ctx.bindings[i];
        let ty = self.path_type(&b.ty, &path);
        let method_span = Span::new(base.span.end + 1, e.span.end - 2);
        if !self.is_clone(&ty) {
            return Err(Diagnostic::new(
                "E0599",
                &format!("no method named `clone` found for `{ty}` in the current scope"),
            )
            .with(Label::primary(method_span, &format!("method not found in `{ty}`")))
            .note("note: `clone` is the method of the trait `Clone`, which this type does not implement"));
        }
        let conflicts: Vec<&Move> = b
            .moves
            .iter()
            .filter(|m| path.starts_with(&m.path) || m.path.starts_with(&path))
            .collect();
        if !conflicts.is_empty() {
            let mut d = Diagnostic::new(
                "E0382",
                &format!("borrow of moved value: `{}`", place_name(&b.name, &path)),
            );
            if conflicts.iter().any(|m| m.path.is_empty()) {
                d = d.with(Label::secondary(
                    b.decl,
                    &format!(
                        "move occurs because `{}` has type `{}`, which does not implement the `Copy` trait",
                        b.name, b.ty
                    ),
                ));
            }
            for m in &conflicts {
                d = move_labels(d, m, &b.name);
            }
            return Err(
                d.with(Label::primary(base.span, "value borrowed here after move"))
            );
        }
        ctx.bindings[i].uses += 1;
        Ok((ty, ctx, "Clone", vec![]))
    }

    fn infer_struct(
        &mut self,
        ctx: Ctx,
        e: &Expr,
        name: &Ident,
        fields: &[(Ident, Expr)],
    ) -> Result<(Ty, Ctx, &'static str, Vec<Derivation>), Diagnostic> {
        let Some(def) = self.program.structure(&name.name) else {
            return Err(Diagnostic::new(
                "E0422",
                &format!("cannot find struct `{}` in this scope", name.name),
            )
            .with(Label::primary(name.span, "not found in this scope")));
        };
        for (f, _) in fields {
            if !def.fields.iter().any(|(g, _, _)| g.name == f.name) {
                return Err(Diagnostic::new(
                    "E0560",
                    &format!("struct `{}` has no field named `{}`", name.name, f.name),
                )
                .with(Label::primary(f.span, "unknown field")));
            }
        }
        for (g, _, _) in &def.fields {
            if !fields.iter().any(|(f, _)| f.name == g.name) {
                return Err(Diagnostic::new(
                    "E0063",
                    &format!(
                        "missing field `{}` in initializer of `{}`",
                        g.name, name.name
                    ),
                )
                .with(Label::primary(e.span, &format!("missing `{}`", g.name))));
            }
        }
        let mut ctx = ctx;
        let mut premises = Vec::new();
        for (f, value) in fields {
            let want = def
                .fields
                .iter()
                .find(|(g, _, _)| g.name == f.name)
                .map(|(_, t, _)| t.clone());
            let checked = self.infer(ctx, value, want.as_ref())?;
            ctx = checked.ctx;
            premises.push(checked.deriv);
        }
        Ok((Ty::Named(name.name.clone()), ctx, "Struct", premises))
    }
}

/// The labels that say where a value was moved.
fn move_labels(d: Diagnostic, m: &Move, name: &str) -> Diagnostic {
    match m.kind {
        MoveKind::Plain => d.with(Label::secondary(m.span, "value moved here")),
        MoveKind::IntoClosure { use_span } => d
            .with(Label::secondary(m.span, "value moved into closure here"))
            .with(Label::secondary(
                use_span,
                "variable moved due to use in closure",
            )),
        MoveKind::Call => d.with(Label::secondary(
            m.span,
            &format!("`{name}` moved due to this call"),
        )),
    }
}

/// Make sure the premise of a binding rule shows its bound variables, even
/// those that the body does not use (rule A-Abs puts them in the context).
fn with_binders(deriv: &mut Derivation, binders: &[(&Ident, &Ty)]) {
    for (x, t) in binders {
        if !deriv.ctx.iter().any(|(y, _)| *y == x.name) {
            deriv.ctx.push((x.name.clone(), (*t).clone()));
        }
    }
}

fn mismatch(span: Span, want: &Ty, found: &Ty) -> Diagnostic {
    Diagnostic::new("E0308", "mismatched types").with(Label::primary(
        span,
        &format!("expected `{want}`, found `{found}`"),
    ))
}

fn arity(span: Span, want: usize, found: usize) -> Diagnostic {
    let s = |n: usize| if n == 1 { "" } else { "s" };
    Diagnostic::new(
        "E0061",
        &format!(
            "this function takes {want} argument{} but {found} argument{} were supplied",
            s(want),
            s(found)
        ),
    )
    .with(Label::primary(span, ""))
}
