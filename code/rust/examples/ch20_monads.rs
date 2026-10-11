// harness: run
//! Monads in everyday Rust: `?` and `and_then` as bind for `Option` and
//! `Result`, `flat_map` as bind for lists, the three monad laws checked on
//! samples, and a state monad built from boxed closures.
//!
//! Run with: `cargo run --example ch20_monads`

use std::num::ParseIntError;

// ANCHOR: kleisli_arrows
/// Parse a quantity: fails on text that is not a number.
fn parse_qty(s: &str) -> Option<u32> {
    s.trim().parse().ok()
}

/// Accept quantities between 1 and 100.
fn check_qty(n: u32) -> Option<u32> {
    if (1..=100).contains(&n) {
        Some(n)
    } else {
        None
    }
}
// ANCHOR_END: kleisli_arrows

// ANCHOR: compose_option
/// Kleisli composition for `Option`: run `f`, and if it produced a value,
/// run `g` on it.
fn compose_option<A, B, C>(
    f: impl Fn(A) -> Option<B>,
    g: impl Fn(B) -> Option<C>,
) -> impl Fn(A) -> Option<C> {
    move |a| f(a).and_then(|b| g(b))
}
// ANCHOR_END: compose_option

// ANCHOR: three_ways
/// With `?`: every `?` is a bind, and the rest of the function body is the
/// continuation that receives the value.
fn boxes_question(s: &str) -> Option<u32> {
    let n = parse_qty(s)?;
    let q = check_qty(n)?;
    Some(q.div_ceil(2))
}

/// With `and_then`: the continuations are written as closures.
fn boxes_and_then(s: &str) -> Option<u32> {
    parse_qty(s).and_then(|n| check_qty(n).and_then(|q| Some(q.div_ceil(2))))
}

/// With `match` and `return`: what `?` does on an `Option`, written out.
fn boxes_match(s: &str) -> Option<u32> {
    let n = match parse_qty(s) {
        Some(v) => v,
        None => return None,
    };
    let q = match check_qty(n) {
        Some(v) => v,
        None => return None,
    };
    Some(q.div_ceil(2))
}
// ANCHOR_END: three_ways

// ANCHOR: result_question
#[derive(Debug, PartialEq)]
enum OrderError {
    BadNumber(ParseIntError),
    OutOfRange(u32),
}

impl From<ParseIntError> for OrderError {
    fn from(e: ParseIntError) -> Self {
        OrderError::BadNumber(e)
    }
}

fn check_range(n: u32) -> Result<u32, OrderError> {
    if (1..=100).contains(&n) {
        Ok(n)
    } else {
        Err(OrderError::OutOfRange(n))
    }
}

/// `?` on a `Result`: bind, plus a conversion of the error through `From`.
fn boxes_result(s: &str) -> Result<u32, OrderError> {
    let n: u32 = s.trim().parse()?;
    let q = check_range(n)?;
    Ok(q.div_ceil(2))
}

/// The same function with the early returns and conversions written out.
fn boxes_result_desugared(s: &str) -> Result<u32, OrderError> {
    let n: u32 = match s.trim().parse::<u32>() {
        Ok(v) => v,
        Err(e) => return Err(From::from(e)),
    };
    let q = match check_range(n) {
        Ok(v) => v,
        Err(e) => return Err(From::from(e)),
    };
    Ok(q.div_ceil(2))
}
// ANCHOR_END: result_question

// ANCHOR: flat_map
/// Every warehouse that stocks `item`.
fn warehouses(item: &str) -> Vec<&'static str> {
    match item {
        "bolts" => vec!["Hamburg", "Lyon"],
        "nuts" => vec!["Lyon"],
        _ => vec![],
    }
}

/// Every carrier that collects from a warehouse.
fn carriers(site: &str) -> Vec<&'static str> {
    match site {
        "Hamburg" => vec!["DHL", "UPS"],
        "Lyon" => vec!["Geodis"],
        _ => vec![],
    }
}

/// `bind` for vectors: apply `f` to every element and concatenate.
fn bind_vec<A, B>(m: Vec<A>, f: impl FnMut(A) -> Vec<B>) -> Vec<B> {
    m.into_iter().flat_map(f).collect()
}

/// Every (warehouse, carrier) pair that can ship `item`.
fn shipping_options(item: &str) -> Vec<(&'static str, &'static str)> {
    bind_vec(warehouses(item), |w| {
        bind_vec(carriers(w), |c| vec![(w, c)])
    })
}
// ANCHOR_END: flat_map

/// The services each carrier offers (a third Kleisli arrow for the laws).
fn services(carrier: &str) -> Vec<String> {
    vec![format!("{carrier} standard"), format!("{carrier} express")]
}

// ANCHOR: laws
/// The three monad laws, checked on samples: for `Option` (pure = `Some`,
/// bind = `and_then`) and for `Vec` (pure = `vec![a]`, bind = `flat_map`).
fn check_laws() {
    for s in ["12", "twelve", "500", "0", " 7 "] {
        let m = parse_qty(s);
        // Left identity: pure(a) >>= f  ==  f(a)
        assert_eq!(Some(s).and_then(parse_qty), parse_qty(s));
        // Right identity: m >>= pure  ==  m
        assert_eq!(m.and_then(Some), m);
        // Associativity: (m >>= f) >>= g  ==  m >>= (|x| f(x) >>= g)
        let half = |n: u32| n.checked_sub(1).map(|k| k / 2);
        assert_eq!(
            m.and_then(check_qty).and_then(half),
            m.and_then(|n| check_qty(n).and_then(half))
        );
    }
    for item in ["bolts", "nuts", "screws"] {
        let m = warehouses(item);
        assert_eq!(bind_vec(vec![item], warehouses), warehouses(item));
        assert_eq!(bind_vec(m.clone(), |x| vec![x]), m);
        assert_eq!(
            bind_vec(bind_vec(m.clone(), carriers), services),
            bind_vec(m.clone(), |w| bind_vec(carriers(w), services))
        );
    }
}
// ANCHOR_END: laws

// ANCHOR: state_monad
/// A stateful computation: a function from the current state to a result and
/// a new state. It is boxed because every closure has its own type, and
/// `bind` must return one type, whatever closure it was given.
struct State<'a, S, A>(Box<dyn FnOnce(S) -> (A, S) + 'a>);

impl<'a, S: 'a, A: 'a> State<'a, S, A> {
    fn pure(a: A) -> Self {
        State(Box::new(move |s| (a, s)))
    }

    fn bind<B: 'a>(self, f: impl FnOnce(A) -> State<'a, S, B> + 'a) -> State<'a, S, B> {
        State(Box::new(move |s| {
            let (a, s1) = (self.0)(s);
            (f(a).0)(s1)
        }))
    }

    fn run(self, initial: S) -> (A, S) {
        (self.0)(initial)
    }
}

/// Read the state.
fn get<'a, S: Clone + 'a>() -> State<'a, S, S> {
    State(Box::new(|s: S| (s.clone(), s)))
}

/// Replace the state.
fn put<'a, S: 'a>(new: S) -> State<'a, S, ()> {
    State(Box::new(move |_| ((), new)))
}
// ANCHOR_END: state_monad

// ANCHOR: label
/// A fresh ticket number: read the counter, advance it, return the old value.
fn fresh<'a>() -> State<'a, u32, u32> {
    get().bind(|n| put(n + 1).bind(move |()| State::pure(n)))
}

/// Give every order line a ticket number, as `label` does in `State.lean`.
fn label<'a>(items: &'a [&'a str]) -> State<'a, u32, Vec<(u32, &'a str)>> {
    match items.split_first() {
        None => State::pure(Vec::new()),
        Some((first, rest)) => fresh().bind(move |n| {
            label(rest).bind(move |tail| {
                let mut lines = vec![(n, *first)];
                lines.extend(tail);
                State::pure(lines)
            })
        }),
    }
}

/// What a Rust programmer writes instead: the state is a `&mut` borrow.
fn label_mut<'a>(items: &[&'a str], counter: &mut u32) -> Vec<(u32, &'a str)> {
    let mut lines = Vec::new();
    for item in items {
        lines.push((*counter, *item));
        *counter += 1;
    }
    lines
}
// ANCHOR_END: label

fn main() {
    println!("-- Option: ?, and_then and match agree --");
    let read_qty = compose_option(parse_qty, check_qty);
    for s in ["12", "twelve", "500"] {
        let boxes = boxes_question(s);
        assert_eq!(boxes, boxes_and_then(s));
        assert_eq!(boxes, boxes_match(s));
        println!("{s:>8}: read_qty = {:?}, boxes = {boxes:?}", read_qty(s));
    }

    println!("-- Result: ? converts errors with From --");
    for s in ["12", "twelve", "500"] {
        let boxes = boxes_result(s);
        assert_eq!(boxes, boxes_result_desugared(s));
        println!("{s:>8}: {boxes:?}");
    }

    println!("-- Vec: flat_map is bind --");
    for item in ["bolts", "nuts", "screws"] {
        println!("{item:>8}: {:?}", shipping_options(item));
    }

    check_laws();
    println!("-- the monad laws hold on every sample --");

    println!("-- State: a monad of closures, and &mut --");
    let items = ["bolts", "nuts", "washers"];
    let (lines, counter) = label(&items).run(100);
    println!("label     : {lines:?}, counter = {counter}");
    let mut counter_mut = 100;
    let lines_mut = label_mut(&items, &mut counter_mut);
    assert_eq!((lines, counter), (lines_mut, counter_mut));
    println!("label_mut : same lines, counter = {counter_mut}");
}
