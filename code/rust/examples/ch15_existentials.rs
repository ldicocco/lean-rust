// harness: run
//! Existential types in Rust: a counter abstraction used through the three
//! quantifier placements (a generic parameter, `impl Trait` in return
//! position, `dyn Trait`), an abstract data type in the style of an ML module
//! (a trait with an associated type), and the encoding of an existential with
//! a universal (a client trait with a generic method).
//!
//! Run with: `cargo run --example ch15_existentials`

// ANCHOR: counter
/// The interface: a counter can take a step and report its value.
trait Counter {
    fn step(&mut self);
    fn get(&self) -> u32;
}

/// Counts by one.
struct Simple(u32);

impl Counter for Simple {
    fn step(&mut self) {
        self.0 += 1;
    }
    fn get(&self) -> u32 {
        self.0
    }
}

/// Counts by one and keeps a log: a different representation with the same
/// observable behavior.
struct Logged {
    count: u32,
    log: Vec<String>,
}

impl Counter for Logged {
    fn step(&mut self) {
        self.count += 1;
        self.log.push(format!("step {}", self.count));
    }
    fn get(&self) -> u32 {
        self.count
    }
}

/// Counts by a fixed stride: different behavior, too.
struct Stride {
    value: u32,
    by: u32,
}

impl Counter for Stride {
    fn step(&mut self) {
        self.value += self.by;
    }
    fn get(&self) -> u32 {
        self.value
    }
}
// ANCHOR_END: counter

// ANCHOR: universal
/// ∀C. Counter C ⇒ C → u32 → u32. The *caller* chooses `C`.
fn run_generic<C: Counter>(mut counter: C, steps: u32) -> u32 {
    for _ in 0..steps {
        counter.step();
    }
    counter.get()
}

/// The same quantifier, written with `impl Trait` in argument position.
fn run_impl(mut counter: impl Counter, steps: u32) -> u32 {
    for _ in 0..steps {
        counter.step();
    }
    counter.get()
}
// ANCHOR_END: universal

// ANCHOR: existential_static
/// ∃C. Counter C ∧ C. The *callee* chooses the type (here `Logged`); the
/// caller only learns that it implements `Counter`.
fn make_counter() -> impl Counter {
    Logged {
        count: 0,
        log: Vec::new(),
    }
}
// ANCHOR_END: existential_static

// ANCHOR: existential_dynamic
/// The witness type is chosen at run time, so it can differ from call to
/// call. The value is packed together with its vtable behind a pointer.
fn make_counter_dyn(kind: &str) -> Box<dyn Counter> {
    match kind {
        "simple" => Box::new(Simple(0)),
        "logged" => Box::new(Logged {
            count: 0,
            log: Vec::new(),
        }),
        _ => Box::new(Stride { value: 0, by: 10 }),
    }
}

/// Unpacking: the client works with any hidden type, through the interface.
fn run_dyn(counter: &mut dyn Counter, steps: u32) -> u32 {
    for _ in 0..steps {
        counter.step();
    }
    counter.get()
}
// ANCHOR_END: existential_dynamic

// ANCHOR: module
/// An abstract data type in the style of Mitchell and Plotkin:
/// ∃S. { init: S, step: S → S, get: S → u32 }. The hidden type is the
/// associated type `State`; a value of a type implementing `CounterModule`
/// is the package of operations.
trait CounterModule {
    type State;
    fn init(&self) -> Self::State;
    fn step(&self, state: Self::State) -> Self::State;
    fn get(&self, state: &Self::State) -> u32;
    /// A binary operation: fine here, because every state of this module has
    /// the same hidden type.
    fn merge(&self, a: Self::State, b: Self::State) -> Self::State;
}

struct UnaryCounters;

impl CounterModule for UnaryCounters {
    /// One `()` per step: a deliberately different representation.
    type State = Vec<()>;
    fn init(&self) -> Vec<()> {
        Vec::new()
    }
    fn step(&self, mut state: Vec<()>) -> Vec<()> {
        state.push(());
        state
    }
    fn get(&self, state: &Vec<()>) -> u32 {
        state.len() as u32
    }
    fn merge(&self, mut a: Vec<()>, b: Vec<()>) -> Vec<()> {
        a.extend(b);
        a
    }
}

/// The package is returned as `impl CounterModule`: callers cannot learn
/// that the states are vectors.
fn counter_module() -> impl CounterModule {
    UnaryCounters
}

/// A client of the module. It manipulates states of type `M::State` without
/// knowing what they are.
fn two_runs<M: CounterModule>(module: &M, first: u32, second: u32) -> u32 {
    let mut a = module.init();
    for _ in 0..first {
        a = module.step(a);
    }
    let mut b = module.init();
    for _ in 0..second {
        b = module.step(b);
    }
    module.get(&module.merge(a, b))
}
// ANCHOR_END: module

// ANCHOR: cps
/// A client that works for *every* counter type: ∀C. Counter C ⇒ C → Output.
/// Closures cannot be generic, so the client is a trait with a generic method.
trait CounterClient {
    type Output;
    fn visit<C: Counter>(self, counter: C) -> Self::Output;
}

/// The existential, encoded with a universal: instead of returning a counter
/// of a hidden type, take a client and hand it the counter.
/// ∃C. Counter C ∧ C  ≅  ∀R. (∀C. Counter C ⇒ C → R) → R
fn with_counter<K: CounterClient>(kind: &str, client: K) -> K::Output {
    match kind {
        "simple" => client.visit(Simple(0)),
        "logged" => client.visit(Logged {
            count: 0,
            log: Vec::new(),
        }),
        _ => client.visit(Stride { value: 0, by: 10 }),
    }
}

/// One client: take some steps and report the value.
struct StepAndGet(u32);

impl CounterClient for StepAndGet {
    type Output = u32;
    fn visit<C: Counter>(self, counter: C) -> u32 {
        run_generic(counter, self.0)
    }
}

/// Another client, with a different result type: the name of the hidden type,
/// which this client may print but not use.
struct TypeName;

impl CounterClient for TypeName {
    type Output = &'static str;
    fn visit<C: Counter>(self, _counter: C) -> &'static str {
        std::any::type_name::<C>()
    }
}
// ANCHOR_END: cps

fn main() {
    // ANCHOR: run_universal
    println!(
        "generic:    {} {}",
        run_generic(Simple(0), 3),
        run_impl(Stride { value: 0, by: 10 }, 3)
    );
    // ANCHOR_END: run_universal

    // ANCHOR: run_static
    let counter = make_counter();
    println!("impl Trait: {}", run_generic(counter, 3));
    // ANCHOR_END: run_static

    // ANCHOR: run_dynamic
    // A heterogeneous collection: three different hidden types in one Vec.
    let mut counters: Vec<Box<dyn Counter>> = ["simple", "logged", "stride"]
        .into_iter()
        .map(make_counter_dyn)
        .collect();
    let results: Vec<u32> = counters
        .iter_mut()
        .map(|c| run_dyn(c.as_mut(), 3))
        .collect();
    println!("dyn Trait:  {results:?}");
    // ANCHOR_END: run_dynamic

    // ANCHOR: run_module
    let module = counter_module();
    println!("module:     {}", two_runs(&module, 2, 3));
    // ANCHOR_END: run_module

    // ANCHOR: run_cps
    for kind in ["simple", "logged", "stride"] {
        let value = with_counter(kind, StepAndGet(3));
        let name = with_counter(kind, TypeName);
        println!("cps:        {kind:<7} -> {value:>2}  (hidden type {name})");
    }
    // ANCHOR_END: run_cps
}
