// harness: compile-fail E0038
//! A trait whose methods cannot be called through a vtable is not dyn
//! compatible: `merge` needs a second value of the same hidden type, and
//! `visit` would need one vtable entry for every type `V`.

trait Visitor {
    fn visit(&mut self, value: u32);
}

// ANCHOR: incompatible
trait Mergeable {
    fn total(&self) -> u32;
    fn merge(&self, other: &Self) -> Self;
    fn accept<V: Visitor>(&self, visitor: &mut V);
}

fn store(items: &mut Vec<Box<dyn Mergeable>>) {}
// ANCHOR_END: incompatible
