// harness: run
//! Existential packages in memory: thin and fat pointers measured with
//! `size_of`, and the size and alignment of a hidden type read back from the
//! vtable at run time.
//!
//! Run with: `cargo run --example ch15_fat_pointers`

use std::mem::{align_of_val, size_of, size_of_val};
use std::rc::Rc;

trait Counter {
    fn step(&mut self);
    fn get(&self) -> u32;
}

/// Three counters whose sizes and alignments do not depend on the platform.
struct Small(u16);
struct Simple(u32);
struct Stride {
    value: u32,
    by: u32,
}

impl Counter for Small {
    fn step(&mut self) {
        self.0 += 1;
    }
    fn get(&self) -> u32 {
        self.0 as u32
    }
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

// ANCHOR: words
/// The size of `T` in machine words (8 bytes on a 64-bit machine, 4 on a
/// 32-bit one), so that the output does not depend on the platform.
fn words<T>() -> usize {
    size_of::<T>() / size_of::<usize>()
}

/// Print one row of the table.
fn row<T>(name: &str) {
    println!("{name:<26}{}", words::<T>());
}
// ANCHOR_END: words

fn main() {
    // ANCHOR: pointer_sizes
    println!("{:<26}words", "pointer type");
    row::<&u32>("&u32");
    row::<&[u32; 4]>("&[u32; 4]");
    row::<Box<Simple>>("Box<Simple>");
    row::<fn(u32) -> u32>("fn(u32) -> u32");
    row::<&[u32]>("&[u32]");
    row::<&str>("&str");
    row::<&dyn Counter>("&dyn Counter");
    row::<&mut dyn Counter>("&mut dyn Counter");
    row::<Box<dyn Counter>>("Box<dyn Counter>");
    row::<Rc<dyn Counter>>("Rc<dyn Counter>");
    row::<Option<Box<dyn Counter>>>("Option<Box<dyn Counter>>");
    row::<&dyn Fn(u32) -> u32>("&dyn Fn(u32) -> u32");
    // ANCHOR_END: pointer_sizes

    // ANCHOR: vtable_info
    // Three packages with three different hidden types.
    let mut counters: Vec<Box<dyn Counter>> = vec![
        Box::new(Small(0)),
        Box::new(Simple(0)),
        Box::new(Stride { value: 0, by: 10 }),
    ];
    // The size and alignment of each hidden type are not known statically;
    // `size_of_val` and `align_of_val` read them from the vtable.
    for counter in counters.iter_mut() {
        counter.step();
        let hidden: &dyn Counter = counter.as_ref();
        println!(
            "value {:>2}: hidden type of size {} and alignment {}",
            hidden.get(),
            size_of_val(hidden),
            align_of_val(hidden),
        );
    }
    // ANCHOR_END: vtable_info

    // ANCHOR: slice_meta
    // A slice reference is a fat pointer too: the hidden quantity is a length.
    let readings = [215u32, 218, 221, 219];
    let first_two: &[u32] = &readings[..2];
    let all: &[u32] = &readings;
    println!(
        "slices of length {} and {}: both {} words",
        first_two.len(),
        all.len(),
        words::<&[u32]>()
    );
    // ANCHOR_END: slice_meta
}
