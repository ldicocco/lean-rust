// harness: compile-fail E0277
//! A `dyn Trait` value has no size known at compile time: the size of the
//! hidden type lives in the vtable, so a package must sit behind a pointer.

trait Counter {
    fn get(&self) -> u32;
}

// ANCHOR: unsized
fn value_of(counter: dyn Counter) -> u32 {
    counter.get()
}
// ANCHOR_END: unsized
