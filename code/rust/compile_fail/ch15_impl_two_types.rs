// harness: compile-fail E0308
//! `impl Trait` in return position hides one type, chosen once for the whole
//! function: two branches cannot return two different types.

trait Counter {
    fn step(&mut self);
    fn get(&self) -> u32;
}

struct Simple(u32);
struct Stride {
    value: u32,
    by: u32,
}

impl Counter for Simple {
    fn step(&mut self) {
        self.0 += 1;
    }
    fn get(&self) -> u32 {
        self.0
    }
}

impl Counter for Stride {
    fn step(&mut self) {
        self.value += self.by;
    }
    fn get(&self) -> u32 {
        self.value
    }
}

// ANCHOR: two_types
fn make_counter(fast: bool) -> impl Counter {
    if fast {
        Stride { value: 0, by: 10 }
    } else {
        Simple(0)
    }
}
// ANCHOR_END: two_types
