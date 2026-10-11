// harness: compile-fail E0308
//! `impl Trait` in return position is opaque: the caller cannot rely on the
//! hidden type, even though the compiler knows it.

trait Counter {
    fn step(&mut self);
    fn get(&self) -> u32;
}

struct Simple(u32);

impl Counter for Simple {
    fn step(&mut self) {
        self.0 += 1;
    }
    fn get(&self) -> u32 {
        self.0
    }
}

// ANCHOR: opaque
fn make_counter() -> impl Counter {
    Simple(0)
}

fn peek() -> u32 {
    let counter: Simple = make_counter();
    counter.0
}
// ANCHOR_END: opaque
