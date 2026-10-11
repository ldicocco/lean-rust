//! Substitutions and first-order unification (Robinson, 1965).
//!
//! A substitution maps type variables to types. During inference it grows one
//! binding at a time, so it is stored the way rustc stores its inference
//! variables: as a table indexed by variable, where entry `n` is `Some(t)`
//! once `?n := t` has been decided. A binding may mention variables that are
//! bound later (the table is in *triangular* form), so applying the
//! substitution means following bindings until no bound variable is left.

use crate::types::{TyVar, Type};

// ANCHOR: subst
/// The substitution built so far, as a table of bindings.
#[derive(Default)]
pub struct Subst {
    bindings: Vec<Option<Type>>,
    /// When `Some`, every unification step is recorded here.
    trace: Option<Vec<String>>,
}

/// Why two types cannot be unified.
#[derive(Clone, Debug, PartialEq)]
pub enum UnifyError {
    /// Two different constructors met: `Int` against `Bool`, say.
    Mismatch(Type, Type),
    /// The variable would have to contain itself: `?0 = ?0 -> ?1`.
    Occurs(TyVar, Type),
}

impl Subst {
    pub fn new() -> Subst {
        Subst::default()
    }

    /// A type variable that is not bound and has never been used.
    pub fn fresh(&mut self) -> TyVar {
        self.bindings.push(None);
        TyVar(self.bindings.len() as u32 - 1)
    }

    /// The binding of `v`, if `v` has been solved.
    pub fn lookup(&self, v: TyVar) -> Option<&Type> {
        self.bindings[v.0 as usize].as_ref()
    }

    /// Applies the substitution to a type: every bound variable is replaced
    /// by its binding, recursively, until only unbound variables remain.
    pub fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(v) => match self.lookup(*v) {
                Some(bound) => self.apply(bound),
                None => ty.clone(),
            },
            Type::Con(con, args) => {
                Type::Con(*con, args.iter().map(|a| self.apply(a)).collect())
            }
        }
    }
}
// ANCHOR_END: subst

// ANCHOR: unify
impl Subst {
    /// Extends the substitution so that `left` and `right` become equal, or
    /// explains why that is impossible.
    pub fn unify(&mut self, left: &Type, right: &Type) -> Result<(), UnifyError> {
        self.unify_at(left, right, 0)
    }

    fn unify_at(
        &mut self,
        left: &Type,
        right: &Type,
        depth: usize,
    ) -> Result<(), UnifyError> {
        // Look through variables that are already solved: we always compare
        // the current knowledge about both sides.
        let left = self.shallow(left);
        let right = self.shallow(right);
        self.log(depth, format!("unify {left}  ~  {right}"));
        match (&left, &right) {
            // Rule Delete: a variable is equal to itself.
            (Type::Var(a), Type::Var(b)) if a == b => Ok(()),
            // Rules Orient and Eliminate: solve the variable, unless the
            // occurs check fails.
            (Type::Var(v), other) | (other, Type::Var(v)) => {
                let other = self.apply(other);
                if other.mentions(*v) {
                    self.log(
                        depth + 1,
                        format!("occurs check: ?{} occurs in {other}", v.0),
                    );
                    return Err(UnifyError::Occurs(*v, other));
                }
                self.log(depth + 1, format!("?{} := {other}", v.0));
                self.bindings[v.0 as usize] = Some(other);
                Ok(())
            }
            // Rule Decompose: same constructor, unify the arguments pairwise.
            (Type::Con(c1, args1), Type::Con(c2, args2)) if c1 == c2 => {
                for (a1, a2) in args1.iter().zip(args2) {
                    self.unify_at(a1, a2, depth + 1)?;
                }
                Ok(())
            }
            // Rule Clash: different constructors can never be made equal.
            _ => {
                self.log(depth + 1, format!("clash: {left} is not {right}"));
                Err(UnifyError::Mismatch(self.apply(&left), self.apply(&right)))
            }
        }
    }
    // ANCHOR_END: unify

    /// Follows bindings at the root only: the result is an unbound variable
    /// or a constructor (whose arguments may still contain bound variables).
    fn shallow(&self, ty: &Type) -> Type {
        let mut ty = ty;
        while let Type::Var(v) = ty {
            match self.lookup(*v) {
                Some(bound) => ty = bound,
                None => break,
            }
        }
        ty.clone()
    }

    /// Starts recording a trace of every unification step.
    pub fn start_trace(&mut self) {
        self.trace = Some(Vec::new());
    }

    /// Returns the recorded steps and clears the record (tracing continues).
    pub fn take_trace(&mut self) -> Vec<String> {
        self.trace.as_mut().map(std::mem::take).unwrap_or_default()
    }

    fn log(&mut self, depth: usize, line: String) {
        if let Some(trace) = &mut self.trace {
            trace.push(format!("{}{line}", "  ".repeat(depth)));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(s: &mut Subst) -> Type {
        Type::Var(s.fresh())
    }

    #[test]
    fn unifies_by_solving_variables() {
        // ?0 -> Int  ~  Bool -> ?1   gives ?0 := Bool, ?1 := Int.
        let mut s = Subst::new();
        let (a, b) = (var(&mut s), var(&mut s));
        let left = Type::fun(a.clone(), Type::int());
        let right = Type::fun(Type::bool(), b.clone());
        s.unify(&left, &right).unwrap();
        assert_eq!(s.apply(&a), Type::bool());
        assert_eq!(s.apply(&b), Type::int());
        assert_eq!(s.apply(&left), s.apply(&right));
    }

    #[test]
    fn later_equations_see_earlier_solutions() {
        // ?0 -> ?0  ~  Int -> ?1: after ?0 := Int the second equation is Int ~ ?1.
        let mut s = Subst::new();
        let (a, b) = (var(&mut s), var(&mut s));
        s.unify(
            &Type::fun(a.clone(), a.clone()),
            &Type::fun(Type::int(), b.clone()),
        )
        .unwrap();
        assert_eq!(s.apply(&b), Type::int());
    }

    #[test]
    fn clash_and_occurs_check() {
        let mut s = Subst::new();
        let a = var(&mut s);
        let err = s.unify(
            &Type::fun(Type::int(), a.clone()),
            &Type::fun(Type::bool(), a.clone()),
        );
        assert_eq!(err, Err(UnifyError::Mismatch(Type::int(), Type::bool())));

        let mut s = Subst::new();
        let (a, b) = (var(&mut s), var(&mut s));
        let err = s.unify(&a, &Type::fun(a.clone(), b.clone()));
        assert_eq!(err, Err(UnifyError::Occurs(TyVar(0), Type::fun(a, b))));
    }

    #[test]
    fn occurs_check_looks_through_bindings() {
        // ?1 := List ?0, then ?0 ~ ?1 must fail: ?0 = List ?0 is infinite.
        let mut s = Subst::new();
        let (a, b) = (var(&mut s), var(&mut s));
        s.unify(&b, &Type::list(a.clone())).unwrap();
        assert!(matches!(s.unify(&a, &b), Err(UnifyError::Occurs(..))));
    }

    #[test]
    fn trace_records_the_steps() {
        let mut s = Subst::new();
        s.start_trace();
        let a = var(&mut s);
        s.unify(
            &Type::fun(a.clone(), a),
            &Type::fun(Type::int(), Type::int()),
        )
        .unwrap();
        assert_eq!(
            s.take_trace(),
            vec![
                "unify ?0 -> ?0  ~  Int -> Int",
                "  unify ?0  ~  Int",
                "    ?0 := Int",
                "  unify Int  ~  Int",
            ]
        );
    }
}
