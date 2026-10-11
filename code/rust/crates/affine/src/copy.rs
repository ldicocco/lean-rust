//! Chapter 23: the `Copy` and `Clone` predicates, and the checks that rustc
//! makes on `#[derive(Copy)]`.
//!
//! In the pure affine calculus of Chapter 22 nothing is `Copy` or `Clone`. With
//! [`Discipline::Copy`] the checker uses the predicates below, which follow
//! Rust's rules.

use crate::diagnostic::{Diagnostic, Label};
use crate::syntax::{Program, StructDef, Ty};

/// Which discipline the checker enforces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Discipline {
    /// Chapter 22: pure λ^aff. No type is `Copy`, no type is `Clone`.
    Affine,
    /// Chapter 23: λ^aff with `Copy` types (free, implicit duplication) and
    /// `Clone` types (explicit duplication with `.clone()`).
    Copy,
}

/// The base types that are `Copy`: Rust's scalar types.
pub const COPY_SCALARS: [&str; 9] = [
    "i32", "i64", "u8", "u32", "u64", "usize", "bool", "char", "f64",
];

// ANCHOR: is_copy
/// The `Copy` predicate, decided by the structure of the type, as in rustc.
pub fn is_copy(program: &Program, ty: &Ty) -> bool {
    match ty {
        Ty::Unit => true,
        Ty::Named(name) => {
            COPY_SCALARS.contains(&name.as_str())
                || program.structure(name).is_some_and(|s| derives(s, "Copy"))
        }
        // Promotion: a pair or a sum is Copy when its components are.
        Ty::Tuple(a, b) | Ty::Either(a, b) => {
            is_copy(program, a) && is_copy(program, b)
        }
        // A shared reference is a read permission: duplicating it is harmless.
        // A mutable reference is a unique permission: it is not Copy.
        Ty::Ref { mutable, .. } => !mutable,
        // Closures may own captured resources that their type does not show,
        // an offer `With<A, B>` is a suspended computation over resources, and
        // an `Rc` must count its copies: none of them is Copy.
        Ty::Fn(..) | Ty::With(..) | Ty::Rc(..) => false,
    }
}
// ANCHOR_END: is_copy

// ANCHOR: is_clone
/// The `Clone` predicate: every `Copy` type, plus types with an explicit,
/// possibly expensive duplication (`String`, `Rc<T>`, structs that derive it).
pub fn is_clone(program: &Program, ty: &Ty) -> bool {
    match ty {
        Ty::Unit => true,
        Ty::Named(name) => {
            COPY_SCALARS.contains(&name.as_str())
                || name == "String"
                || program.structure(name).is_some_and(|s| derives(s, "Clone"))
        }
        Ty::Tuple(a, b) | Ty::Either(a, b) => {
            is_clone(program, a) && is_clone(program, b)
        }
        Ty::Ref { mutable, .. } => !mutable,
        Ty::Rc(_) => true,
        Ty::Fn(..) | Ty::With(..) => false,
    }
}
// ANCHOR_END: is_clone

fn derives(s: &StructDef, name: &str) -> bool {
    s.derives.iter().any(|d| d.name == name)
}

// ANCHOR: check_derives
/// The checks rustc makes when a struct derives `Copy`: `Clone` must be
/// derived too (E0277), every field must be `Copy` (E0204), and the type must
/// not have a destructor (E0184).
pub fn check_derives(program: &Program, s: &StructDef) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    let Some(copy) = s.derives.iter().find(|d| d.name == "Copy") else {
        return errors;
    };
    let name = &s.name.name;
    if !derives(s, "Clone") {
        errors.push(
            Diagnostic::new(
                "E0277",
                &format!("the trait bound `{name}: Clone` is not satisfied"),
            )
            .with(Label::secondary(
                copy.span,
                "in this derive macro expansion",
            ))
            .with(Label::primary(
                s.name.span,
                &format!("the trait `Clone` is not implemented for `{name}`"),
            ))
            .note("note: `Copy` requires `Clone`: `pub trait Copy: Clone`"),
        );
    }
    let bad_fields: Vec<_> = s
        .fields
        .iter()
        .filter(|(_, ty, _)| !is_copy(program, ty))
        .collect();
    if !bad_fields.is_empty() {
        let mut d = Diagnostic::new(
            "E0204",
            "the trait `Copy` cannot be implemented for this type",
        )
        .with(Label::secondary(
            copy.span,
            "in this derive macro expansion",
        ))
        .with(Label::primary(s.name.span, ""));
        for (_, _, span) in bad_fields {
            d = d.with(Label::secondary(
                *span,
                "this field does not implement `Copy`",
            ));
        }
        errors.push(d);
    }
    if let Some(span) = program.items.iter().find_map(|item| match item {
        crate::syntax::Item::DropImpl { ty, span } if ty.name == *name => Some(*span),
        _ => None,
    }) {
        errors.push(
            Diagnostic::new(
                "E0184",
                "the trait `Copy` cannot be implemented for this type; the type has a destructor",
            )
            .with(Label::secondary(copy.span, "in this derive macro expansion"))
            .with(Label::primary(s.name.span, "`Copy` not allowed on types with destructors"))
            .child("destructor declared here", Label::primary(span, "")),
        );
    }
    errors
}
// ANCHOR_END: check_derives

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_program;

    fn program() -> Program {
        parse_program(
            "#[derive(Clone, Copy)] struct Point { x: i32, y: i32 }
             #[derive(Clone)] struct Reading { sensor: String, value: f64 }
             struct Handle { fd: i32 }",
        )
        .unwrap()
    }

    #[test]
    fn copy_follows_the_structure_of_types() {
        let p = program();
        let t = |s: &str| {
            crate::parser::parse_program(&format!("fn f(x: {s});"))
                .unwrap()
                .function("f")
                .unwrap()
                .params[0]
                .1
                .clone()
        };
        assert!(is_copy(&p, &t("i32")));
        assert!(is_copy(&p, &t("(i32, (bool, ()))")));
        assert!(is_copy(&p, &t("Point")));
        assert!(is_copy(&p, &t("&String")));
        assert!(!is_copy(&p, &t("&mut i32")));
        assert!(!is_copy(&p, &t("String")));
        assert!(!is_copy(&p, &t("(i32, String)")));
        assert!(!is_copy(&p, &t("Reading")));
        assert!(!is_copy(&p, &t("Handle")));
        assert!(!is_copy(&p, &t("FnOnce(i32) -> i32")));
        assert!(!is_copy(&p, &t("Rc<i32>")));
        assert!(is_clone(&p, &t("Rc<String>")));
        assert!(is_clone(&p, &t("Reading")));
        assert!(!is_clone(&p, &t("Handle")));
        assert!(!is_clone(&p, &t("File")));
    }

    #[test]
    fn derive_copy_is_checked() {
        let p = parse_program(
            "#[derive(Clone, Copy)] struct Reading { sensor: String, value: f64 }
             #[derive(Clone, Copy)] struct Token { id: u64 }
             impl Drop for Token {}
             #[derive(Copy)] struct Pixel { x: i32 }",
        )
        .unwrap();
        let codes: Vec<String> = p
            .items
            .iter()
            .filter_map(|item| match item {
                crate::syntax::Item::Struct(s) => Some(check_derives(&p, s)),
                _ => None,
            })
            .flatten()
            .filter_map(|d| d.code)
            .collect();
        assert_eq!(codes, ["E0204", "E0184", "E0277"]);
    }
}
