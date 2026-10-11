// harness: run
//! A zipper for expression trees: the derivative of a recursive type, put to
//! work in a small editor that moves a cursor through an expression and
//! rewrites the subexpression under it.
//!
//! Demonstrates: one-hole contexts as an `enum` with one variant per position
//! in each constructor (the terms of the derivative), plugging a value into a
//! hole, and a cursor that moves up and down in constant time per step.
//!
//! Run with: `cargo run --example ch11_zipper`

use std::fmt;

// ANCHOR: expr
/// Expressions: E = Num + Var + E × E + E × E.
#[derive(Clone, Debug, PartialEq)]
enum Expr {
    Num(i64),
    Var(char),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}
// ANCHOR_END: expr

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Num(n) => write!(f, "{n}"),
            Expr::Var(v) => write!(f, "{v}"),
            Expr::Add(a, b) => write!(f, "({a} + {b})"),
            Expr::Mul(a, b) => write!(f, "({a} * {b})"),
        }
    }
}

fn num(n: i64) -> Expr {
    Expr::Num(n)
}
fn var(v: char) -> Expr {
    Expr::Var(v)
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(Box::new(a), Box::new(b))
}
fn mul(a: Expr, b: Expr) -> Expr {
    Expr::Mul(Box::new(a), Box::new(b))
}

// ANCHOR: frame
/// One step on the way from the root down to the cursor: which operand of
/// which constructor we went into, and the operand we left behind. These four
/// variants are the four terms of the derivative ∂E = E + E + E + E: the
/// constants `Num` and `Var` contribute nothing, and each `E × E` contributes
/// "hole on the left, keep the right" plus "keep the left, hole on the right".
#[derive(Clone, Debug)]
enum Frame {
    AddLeft(Expr),
    AddRight(Expr),
    MulLeft(Expr),
    MulRight(Expr),
}

/// Fill the hole of a frame with an expression.
fn plug(frame: Frame, e: Expr) -> Expr {
    match frame {
        Frame::AddLeft(right) => add(e, right),
        Frame::AddRight(left) => add(left, e),
        Frame::MulLeft(right) => mul(e, right),
        Frame::MulRight(left) => mul(left, e),
    }
}
// ANCHOR_END: frame

// ANCHOR: zipper
/// The cursor: the subexpression in focus, and the path of frames from the
/// root down to it (innermost frame last).
#[derive(Clone, Debug)]
struct Zipper {
    focus: Expr,
    path: Vec<Frame>,
}

impl Zipper {
    fn new(e: Expr) -> Zipper {
        Zipper {
            focus: e,
            path: Vec::new(),
        }
    }

    /// Move into the left operand. Fails on a leaf.
    fn left(mut self) -> Option<Zipper> {
        let (child, frame) = match self.focus {
            Expr::Add(a, b) => (*a, Frame::AddLeft(*b)),
            Expr::Mul(a, b) => (*a, Frame::MulLeft(*b)),
            Expr::Num(_) | Expr::Var(_) => return None,
        };
        self.path.push(frame);
        Some(Zipper {
            focus: child,
            path: self.path,
        })
    }

    /// Move into the right operand. Fails on a leaf.
    fn right(mut self) -> Option<Zipper> {
        let (child, frame) = match self.focus {
            Expr::Add(a, b) => (*b, Frame::AddRight(*a)),
            Expr::Mul(a, b) => (*b, Frame::MulRight(*a)),
            Expr::Num(_) | Expr::Var(_) => return None,
        };
        self.path.push(frame);
        Some(Zipper {
            focus: child,
            path: self.path,
        })
    }

    /// Move to the parent: plug the focus into the innermost frame.
    fn up(mut self) -> Option<Zipper> {
        let frame = self.path.pop()?;
        Some(Zipper {
            focus: plug(frame, self.focus),
            path: self.path,
        })
    }

    /// Replace the subexpression under the cursor.
    fn replace(self, e: Expr) -> Zipper {
        Zipper {
            focus: e,
            path: self.path,
        }
    }

    /// Close the zipper: plug the focus into every frame, innermost first.
    fn rebuild(self) -> Expr {
        self.path
            .into_iter()
            .rev()
            .fold(self.focus, |e, frame| plug(frame, e))
    }

    /// The whole expression with a hole `[ ]` where the cursor is.
    fn context(&self) -> String {
        let mut text = String::from("[ ]");
        for frame in self.path.iter().rev() {
            text = match frame {
                Frame::AddLeft(r) => format!("({text} + {r})"),
                Frame::AddRight(l) => format!("({l} + {text})"),
                Frame::MulLeft(r) => format!("({text} * {r})"),
                Frame::MulRight(l) => format!("({l} * {text})"),
            };
        }
        text
    }
}
// ANCHOR_END: zipper

// ANCHOR: simplify
/// Simplify the node under the cursor using x + 0 = x and x * 1 = x.
fn simplify_here(z: Zipper) -> Zipper {
    let simpler = match &z.focus {
        Expr::Add(a, b) if **b == num(0) => Some((**a).clone()),
        Expr::Mul(a, b) if **b == num(1) => Some((**a).clone()),
        _ => None,
    };
    match simpler {
        Some(e) => z.replace(e),
        None => z,
    }
}
// ANCHOR_END: simplify

fn show(step: &str, z: &Zipper) {
    println!(
        "{step:<14} focus = {:<10} context = {}",
        z.focus.to_string(),
        z.context()
    );
}

fn main() {
    // ANCHOR: run
    let e = mul(add(var('x'), num(0)), add(var('y'), mul(var('z'), num(1))));
    println!("start: {e}");

    let z = Zipper::new(e);
    show("root", &z);
    let z = z.left().expect("a product has a left operand");
    show("left", &z);
    let z = simplify_here(z);
    show("simplify", &z);
    let z = z.up().expect("not at the root");
    let z = z.right().and_then(Zipper::right).expect("two steps right");
    show("right, right", &z);
    let z = simplify_here(z);
    show("simplify", &z);

    let result = z.rebuild();
    println!("result: {result}");
    assert_eq!(result, mul(var('x'), add(var('y'), var('z'))));
    // ANCHOR_END: run

    // Going down and back up again changes nothing.
    let e = add(num(1), mul(num(2), num(3)));
    let round_trip = Zipper::new(e.clone()).right().and_then(Zipper::up);
    assert_eq!(round_trip.map(Zipper::rebuild), Some(e));
}
