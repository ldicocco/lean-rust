// harness: run
//! `dyn Any`: the existential that can be opened. Downcasting recovers the
//! hidden type at run time, which is useful (type-indexed maps, error
//! inspection) and breaks the promises that parametric types make.
//!
//! Run with: `cargo run --example ch15_any`

use std::any::{Any, TypeId};
use std::collections::BTreeMap;
use std::error::Error;
use std::num::ParseIntError;

// ANCHOR: describe
/// A `&dyn Any` hides its type, but `downcast_ref` asks "is it a `T`?" and,
/// if so, returns the value at type `T`.
fn describe(value: &dyn Any) -> String {
    if let Some(n) = value.downcast_ref::<i32>() {
        format!("an i32: {n}")
    } else if let Some(s) = value.downcast_ref::<String>() {
        format!("a String of length {}", s.len())
    } else if let Some(b) = value.downcast_ref::<bool>() {
        format!("a bool: {b}")
    } else {
        "something else".to_string()
    }
}
// ANCHOR_END: describe

// ANCHOR: not_identity
/// The signature looks like ∀T. T → T, whose only total, parametric
/// inhabitant is the identity. The bound `T: Any` is the warning sign: the
/// body may look at the type, and it does.
fn not_identity<T: Any>(mut value: T) -> T {
    if let Some(n) = (&mut value as &mut dyn Any).downcast_mut::<i32>() {
        *n += 1;
    }
    value
}
// ANCHOR_END: not_identity

// ANCHOR: type_map
/// A map with at most one value per *type*, as used for request extensions
/// and plugin registries. The key is the hidden type's `TypeId`.
#[derive(Default)]
struct Extensions {
    values: BTreeMap<TypeId, Box<dyn Any>>,
}

impl Extensions {
    fn insert<T: Any>(&mut self, value: T) {
        self.values.insert(TypeId::of::<T>(), Box::new(value));
    }

    fn get<T: Any>(&self) -> Option<&T> {
        self.values.get(&TypeId::of::<T>())?.downcast_ref::<T>()
    }
}

struct RequestId(u64);

struct Operator(String);
// ANCHOR_END: type_map

// ANCHOR: errors
/// `Box<dyn Error>` hides the type of the error; a caller that cares can
/// downcast to the concrete error types it knows how to handle.
fn parse_reading(text: &str) -> Result<i64, Box<dyn Error>> {
    let value: i64 = text.trim().parse()?;
    if value < -2730 {
        return Err("below absolute zero".into());
    }
    Ok(value)
}

fn classify(result: Result<i64, Box<dyn Error>>) -> String {
    match result {
        Ok(v) => format!("ok: {v}"),
        Err(e) => match e.downcast_ref::<ParseIntError>() {
            Some(parse) => format!("not a number ({parse})"),
            None => format!("invalid reading ({e})"),
        },
    }
}
// ANCHOR_END: errors

fn main() {
    // ANCHOR: run_describe
    let packages: Vec<Box<dyn Any>> = vec![
        Box::new(42i32),
        Box::new(String::from("fridge")),
        Box::new(1.5f64),
    ];
    for p in &packages {
        println!("{}", describe(p.as_ref()));
    }
    // ANCHOR_END: run_describe

    // ANCHOR: run_not_identity
    println!(
        "not_identity: {} {:?} {}",
        not_identity(41i32),
        not_identity("unchanged"),
        not_identity(41i64)
    );
    // ANCHOR_END: run_not_identity

    // ANCHOR: run_type_map
    let mut ext = Extensions::default();
    ext.insert(RequestId(7));
    ext.insert(Operator("ada".to_string()));
    let id: Option<&RequestId> = ext.get::<RequestId>();
    let operator: Option<&Operator> = ext.get::<Operator>();
    println!("request id: {:?}", id.map(|r| r.0));
    println!("operator:   {:?}", operator.map(|o| o.0.as_str()));
    println!("a u8:       {:?}", ext.get::<u8>());
    // ANCHOR_END: run_type_map

    // ANCHOR: run_errors
    for text in ["215", "21.5", "-3000"] {
        println!("{text:>6}: {}", classify(parse_reading(text)));
    }
    // ANCHOR_END: run_errors
}
