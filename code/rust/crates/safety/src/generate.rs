//! Random terms. The main generator is *type-directed*: asked for a term of a
//! given type, it picks a typing rule whose conclusion has that type and
//! generates the premises recursively. It runs the typing rules backwards, so
//! everything it produces is well typed by construction (and the property
//! tests check that too).

use crate::rng::Rng;
use crate::syntax::{Term, Ty, add, app, is_zero, ite, lam};
use crate::typing::Rules;

/// A random type: mostly `bool` and `nat`, sometimes a function type.
pub fn gen_type(rng: &mut Rng, depth: usize) -> Ty {
    if depth == 0 || rng.below(3) > 0 {
        if rng.below(2) == 0 { Ty::Bool } else { Ty::Nat }
    } else {
        Ty::arrow(gen_type(rng, depth - 1), gen_type(rng, depth - 1))
    }
}

/// The typing rules that can conclude a term of a given type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Choice {
    Var(usize),
    True,
    False,
    Lit,
    Lam,
    App,
    If,
    Add,
    IsZero,
}

// ANCHOR: gen_term
/// A random term of type `ty` in context `ctx`, with roughly `size`
/// constructors, following the typing rules `rules` backwards.
pub fn gen_term(rng: &mut Rng, rules: Rules, ctx: &[Ty], ty: &Ty, size: usize) -> Term {
    // Collect the rules whose conclusion can have type `ty`.
    let mut choices = Vec::new();
    for (i, var_ty) in ctx.iter().enumerate() {
        if var_ty == ty {
            choices.push(Choice::Var(i)); // T-Var
        }
    }
    match ty {
        Ty::Bool => choices.extend([Choice::True, Choice::False]),
        Ty::Nat => choices.push(Choice::Lit),
        Ty::Arrow(..) => choices.push(Choice::Lam),
    }
    if size > 1 {
        // Rules with premises, when there is room for subterms. Applications
        // are listed twice: they create the β-redexes that make runs long.
        choices.extend([Choice::App, Choice::App, Choice::If]);
        match ty {
            Ty::Nat => choices.push(Choice::Add),
            Ty::Bool => choices.push(Choice::IsZero),
            Ty::Arrow(..) => {}
        }
    }
    let budget = size.saturating_sub(1);
    match *rng.pick(&choices) {
        Choice::Var(i) => Term::Var(i),
        Choice::True => Term::True,
        Choice::False => Term::False,
        Choice::Lit => Term::Lit(rng.below(10) as u64),
        Choice::Lam => {
            // T-Lam: ty is σ → τ; generate a body of type τ with σ in scope.
            let Ty::Arrow(param, result) = ty else {
                unreachable!()
            };
            let mut inner = vec![(**param).clone()];
            inner.extend_from_slice(ctx);
            lam(
                (**param).clone(),
                gen_term(rng, rules, &inner, result, budget),
            )
        }
        Choice::App => {
            // T-App: invent an argument type σ, then a function σ → ty and an
            // argument σ.
            let arg_ty = gen_type(rng, 1);
            let (left, right) = split(rng, budget);
            let f = gen_term(
                rng,
                rules,
                ctx,
                &Ty::arrow(arg_ty.clone(), ty.clone()),
                left,
            );
            app(f, gen_term(rng, rules, ctx, &arg_ty, right))
        }
        Choice::If => {
            // T-If: a boolean condition and two branches of type ty. The broken
            // rule lets the else branch have any type at all.
            let c = gen_term(rng, rules, ctx, &Ty::Bool, budget / 3);
            let t = gen_term(rng, rules, ctx, ty, budget / 3);
            let else_ty = match rules {
                Rules::Sound => ty.clone(),
                Rules::BrokenIf => gen_type(rng, 1),
            };
            ite(c, t, gen_term(rng, rules, ctx, &else_ty, budget / 3))
        }
        Choice::Add => {
            let (left, right) = split(rng, budget);
            let a = gen_term(rng, rules, ctx, &Ty::Nat, left);
            add(a, gen_term(rng, rules, ctx, &Ty::Nat, right))
        }
        Choice::IsZero => is_zero(gen_term(rng, rules, ctx, &Ty::Nat, budget)),
    }
}
// ANCHOR_END: gen_term

/// Splits a size budget between two subterms.
fn split(rng: &mut Rng, budget: usize) -> (usize, usize) {
    let left = rng.below(budget + 1);
    (left, budget - left)
}

/// A random term with no regard for types: closed (every variable is bound),
/// but usually ill typed. Used to see what the type system rules out.
pub fn gen_untyped(rng: &mut Rng, binders: usize, size: usize) -> Term {
    let leaf = |rng: &mut Rng| match rng.below(if binders > 0 { 4 } else { 3 }) {
        0 => Term::True,
        1 => Term::False,
        2 => Term::Lit(rng.below(10) as u64),
        _ => Term::Var(rng.below(binders)),
    };
    if size <= 1 {
        return leaf(rng);
    }
    let budget = size - 1;
    match rng.below(6) {
        0 => lam(gen_type(rng, 1), gen_untyped(rng, binders + 1, budget)),
        1 => {
            let (l, r) = split(rng, budget);
            app(gen_untyped(rng, binders, l), gen_untyped(rng, binders, r))
        }
        2 => ite(
            gen_untyped(rng, binders, budget / 3),
            gen_untyped(rng, binders, budget / 3),
            gen_untyped(rng, binders, budget / 3),
        ),
        3 => {
            let (l, r) = split(rng, budget);
            add(gen_untyped(rng, binders, l), gen_untyped(rng, binders, r))
        }
        4 => is_zero(gen_untyped(rng, binders, budget)),
        _ => leaf(rng),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typing::{type_of, type_of_with};

    #[test]
    fn generated_terms_have_the_requested_type() {
        let mut rng = Rng::new(1);
        for _ in 0..2000 {
            let ty = gen_type(&mut rng, 2);
            let size = 1 + rng.below(25);
            let t = gen_term(&mut rng, Rules::Sound, &[], &ty, size);
            assert_eq!(type_of(&[], &t), Ok(ty), "{t}");
        }
    }

    #[test]
    fn broken_generator_matches_the_broken_checker() {
        let mut rng = Rng::new(2);
        for _ in 0..2000 {
            let ty = gen_type(&mut rng, 2);
            let t = gen_term(&mut rng, Rules::BrokenIf, &[], &ty, 15);
            assert_eq!(type_of_with(Rules::BrokenIf, &[], &t), Ok(ty), "{t}");
        }
    }

    #[test]
    fn untyped_terms_are_closed() {
        let mut rng = Rng::new(3);
        for _ in 0..500 {
            let t = gen_untyped(&mut rng, 0, 12);
            // A closed term never reports an unbound variable.
            if let Err(e) = type_of(&[], &t) {
                assert!(
                    !matches!(e, crate::typing::TypeError::UnboundVariable(_)),
                    "{t}"
                );
            }
        }
    }
}
