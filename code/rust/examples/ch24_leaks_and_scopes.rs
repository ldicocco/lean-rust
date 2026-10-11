// harness: run
//! Affine, not linear: safe Rust can skip a destructor. `mem::forget`,
//! `Box::leak`, a forgotten `Vec::drain` (designed to stay safe when leaked),
//! `Rc` trees with `Weak` back pointers, an `Rc` cycle that leaks, and
//! `thread::scope`, which joins threads without relying on a destructor.
//!
//! Run with: `cargo run --example ch24_leaks_and_scopes`

use std::cell::RefCell;
use std::mem;
use std::rc::{Rc, Weak};
use std::thread;

struct Noisy(&'static str);

impl Drop for Noisy {
    fn drop(&mut self) {
        println!("  drop {}", self.0);
    }
}

// ANCHOR: forget
fn forgetting() {
    let kept = Noisy("kept");
    let forgotten = Noisy("forgotten");
    mem::forget(forgotten); // safe: the destructor will never run
    let leaked: &'static mut Noisy = Box::leak(Box::new(Noisy("leaked")));
    leaked.0 = "leaked (renamed)"; // a `'static` reference to a never-freed box
    println!("  end of scope, still holding {}", kept.0);
}
// ANCHOR_END: forget

// ANCHOR: drain
fn forgotten_drain() {
    let mut readings = vec![10, 11, 12, 13, 14, 15];
    let drain = readings.drain(1..3); // would remove 11 and 12
    mem::forget(drain); // its destructor, which repairs the vector, never runs
    println!("  after forgetting the drain: {readings:?}");
}
// ANCHOR_END: drain

// ANCHOR: tree
/// A node of a tree: children are owned (strong `Rc`), the parent pointer is
/// a `Weak`, which does not keep the parent alive.
struct Node {
    name: &'static str,
    parent: RefCell<Weak<Node>>,
    children: RefCell<Vec<Rc<Node>>>,
}

impl Node {
    fn new(name: &'static str) -> Rc<Node> {
        Rc::new(Node {
            name,
            parent: RefCell::new(Weak::new()),
            children: RefCell::new(Vec::new()),
        })
    }
}

impl Drop for Node {
    fn drop(&mut self) {
        println!("  drop node {}", self.name);
    }
}

fn adopt(parent: &Rc<Node>, child: &Rc<Node>) {
    parent.children.borrow_mut().push(Rc::clone(child));
    *child.parent.borrow_mut() = Rc::downgrade(parent);
}

fn counts(label: &str, node: &Rc<Node>) {
    println!(
        "  {label}: strong = {}, weak = {}",
        Rc::strong_count(node),
        Rc::weak_count(node)
    );
}

fn tree() {
    let lab = Node::new("lab");
    let probe = Node::new("probe");
    adopt(&lab, &probe);
    counts("lab  ", &lab);
    counts("probe", &probe);
    let parent = probe.parent.borrow().upgrade().map(|p| p.name);
    println!("  probe's parent: {parent:?}");
    drop(lab); // the last strong reference to "lab": the whole tree goes
    let parent = probe.parent.borrow().upgrade().map(|p| p.name);
    println!("  probe's parent after drop(lab): {parent:?}");
    counts("probe", &probe);
}
// ANCHOR_END: tree

// ANCHOR: cycle
fn cycle() {
    let a = Node::new("a");
    let b = Node::new("b");
    a.children.borrow_mut().push(Rc::clone(&b)); // a -> b (strong)
    b.children.borrow_mut().push(Rc::clone(&a)); // b -> a (strong): a cycle
    counts("a", &a);
    counts("b", &b);
    println!("  end of scope");
} // a and b lose one strong reference each, but neither count reaches 0
// ANCHOR_END: cycle

// ANCHOR: scope
fn scoped_threads() {
    let samples = vec![3, 1, 4, 1, 5, 9, 2, 6];
    let (left, right) = samples.split_at(samples.len() / 2);
    // Both threads borrow `samples` from this stack frame. `thread::scope`
    // joins them before it returns, so the borrow cannot outlive the data.
    let (sum_left, sum_right) = thread::scope(|s| {
        let h1 = s.spawn(|| left.iter().sum::<i32>());
        let h2 = s.spawn(|| right.iter().sum::<i32>());
        (h1.join().unwrap(), h2.join().unwrap())
    });
    println!(
        "  sums: {sum_left} + {sum_right} = {}",
        sum_left + sum_right
    );
    println!("  samples still owned here: {samples:?}");
}
// ANCHOR_END: scope

fn main() {
    println!("mem::forget and Box::leak:");
    forgetting();
    println!("a forgotten Vec::drain:");
    forgotten_drain();
    println!("a tree with Weak parent pointers:");
    tree();
    println!("a cycle of strong pointers:");
    cycle();
    println!("thread::scope:");
    scoped_threads();
    println!("end of main");
}
