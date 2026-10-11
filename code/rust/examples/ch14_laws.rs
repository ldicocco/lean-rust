// harness: run
//! Laws that Rust cannot state: the monoid laws checked on samples, two
//! instances that break them, and what goes wrong when they are broken (a
//! left-to-right fold and a divide-and-conquer fold stop agreeing). Ends with
//! the chapter's walkthrough: summary statistics of lab measurements, computed
//! per batch and merged.
//!
//! Run with: `cargo run --example ch14_laws`

use std::fmt::Debug;

/// The `Monoid` trait of `ch14_dictionary_passing.rs`, repeated so that this
/// example stands on its own.
trait Monoid {
    fn empty() -> Self;
    fn combine(self, other: Self) -> Self;
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Sum(i64);

impl Monoid for Sum {
    fn empty() -> Self {
        Sum(0)
    }
    fn combine(self, other: Self) -> Self {
        Sum(self.0 + other.0)
    }
}

impl Monoid for String {
    fn empty() -> Self {
        String::new()
    }
    fn combine(mut self, other: Self) -> Self {
        self.push_str(&other);
        self
    }
}

// ANCHOR: unlawful
/// Subtraction with 0 as the "neutral" element. The compiler accepts this
/// instance: the trait only asks for two functions of the right types.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Diff(i64);

impl Monoid for Diff {
    fn empty() -> Self {
        Diff(0)
    }
    fn combine(self, other: Self) -> Self {
        Diff(self.0 - other.0)
    }
}

/// Floating-point addition: associative for real numbers, but not for `f64`,
/// because every addition rounds its result.
#[derive(Clone, Copy, Debug, PartialEq)]
struct FloatSum(f64);

impl Monoid for FloatSum {
    fn empty() -> Self {
        FloatSum(0.0)
    }
    fn combine(self, other: Self) -> Self {
        FloatSum(self.0 + other.0)
    }
}
// ANCHOR_END: unlawful

// ANCHOR: check_laws
/// Check the three monoid laws on every sample (identity) and on every
/// triple of samples (associativity). Returns the number of checks performed,
/// or a description of the first counterexample.
fn check_laws<M>(samples: &[M]) -> Result<usize, String>
where
    M: Monoid + Clone + PartialEq + Debug,
{
    let mut checks = 0;
    for a in samples {
        let left = M::empty().combine(a.clone());
        if left != *a {
            return Err(format!("left identity fails: empty ⋄ {a:?} = {left:?}"));
        }
        let right = a.clone().combine(M::empty());
        if right != *a {
            return Err(format!("right identity fails: {a:?} ⋄ empty = {right:?}"));
        }
        checks += 2;
    }
    for a in samples {
        for b in samples {
            for c in samples {
                let ab_c = a.clone().combine(b.clone()).combine(c.clone());
                let a_bc = a.clone().combine(b.clone().combine(c.clone()));
                if ab_c != a_bc {
                    return Err(format!(
                        "associativity fails for {a:?}, {b:?}, {c:?}\n\
                         (a ⋄ b) ⋄ c = {ab_c:?}, a ⋄ (b ⋄ c) = {a_bc:?}"
                    ));
                }
                checks += 1;
            }
        }
    }
    Ok(checks)
}
// ANCHOR_END: check_laws

// ANCHOR: two_folds
/// Left to right: ((e ⋄ x1) ⋄ x2) ⋄ ... ⋄ xn.
fn mconcat<M: Monoid>(items: Vec<M>) -> M {
    let mut acc = M::empty();
    for item in items {
        acc = acc.combine(item);
    }
    acc
}

/// Divide and conquer: split in halves, combine each half, combine the two
/// results. This is how a parallel reduction splits its work. It computes the
/// same value as `mconcat` exactly when the monoid laws hold.
fn mconcat_tree<M: Monoid>(mut items: Vec<M>) -> M {
    match items.len() {
        0 => M::empty(),
        1 => items.pop().unwrap(),
        n => {
            let right = items.split_off(n / 2);
            mconcat_tree(items).combine(mconcat_tree(right))
        }
    }
}
// ANCHOR_END: two_folds

// ANCHOR: stats
/// Summary statistics of a batch of measurements. Every field is combined by
/// a lawful monoid (sum, sum, min, max), so `Stats` is lawful too.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Stats {
    count: u64,
    total: i64,
    min: i64,
    max: i64,
}

impl Stats {
    /// The statistics of a single measurement.
    fn of(x: i64) -> Stats {
        Stats {
            count: 1,
            total: x,
            min: x,
            max: x,
        }
    }
}

impl Monoid for Stats {
    fn empty() -> Self {
        Stats {
            count: 0,
            total: 0,
            min: i64::MAX,
            max: i64::MIN,
        }
    }
    fn combine(self, other: Self) -> Self {
        Stats {
            count: self.count + other.count,
            total: self.total + other.total,
            min: self.min.min(other.min),
            max: self.max.max(other.max),
        }
    }
}
// ANCHOR_END: stats

fn print_check<M>(name: &str, samples: &[M])
where
    M: Monoid + Clone + PartialEq + Debug,
{
    match check_laws(samples) {
        Ok(n) => println!("  {name:<9} ok ({n} checks)"),
        Err(msg) => {
            // Indent the second line of a message under the first.
            let msg = msg.replace('\n', "\n            ");
            println!("  {name:<9} FAILED: {msg}")
        }
    }
}

fn print_folds<M: Monoid + Clone + Debug>(name: &str, items: Vec<M>) {
    let left = mconcat(items.clone());
    let tree = mconcat_tree(items);
    println!(
        "  {name:<9} left: {:<29} tree: {tree:?}",
        format!("{left:?}")
    );
}

fn main() {
    // ANCHOR: run_checks
    println!("law checks on samples:");
    let ints = [-7, -1, 0, 1, 2, 3, 10];
    print_check("Sum", &ints.map(Sum));
    print_check("String", &["", "a", "bc", "def"].map(String::from));
    print_check("Stats", &ints.map(Stats::of));
    print_check("Diff", &ints.map(Diff));
    print_check("FloatSum", &[0.1, 0.2, 0.3, 1.0e16].map(FloatSum));
    // ANCHOR_END: run_checks

    // ANCHOR: run_folds
    println!("left fold vs tree fold:");
    print_folds("Sum", (1..=6).map(Sum).collect());
    print_folds("Diff", (1..=6).map(Diff).collect());
    print_folds(
        "FloatSum",
        vec![FloatSum(0.1), FloatSum(0.2), FloatSum(0.3)],
    );
    // ANCHOR_END: run_folds

    // ANCHOR: walkthrough
    // Three instruments, three batches of measurements (in tenths of a degree).
    let batches: Vec<Vec<i64>> = vec![
        vec![215, 218, 221, 219],
        vec![202, 199],
        vec![230, 228, 233],
    ];

    // Each instrument summarizes its own batch...
    let per_batch: Vec<Stats> = batches
        .iter()
        .map(|batch| mconcat(batch.iter().map(|&x| Stats::of(x)).collect()))
        .collect();
    // ...and the summaries are merged.
    let merged = mconcat(per_batch.clone());

    // The same statistics, computed in one pass over all the measurements.
    let all: Vec<Stats> = batches.concat().into_iter().map(Stats::of).collect();
    let one_pass = mconcat(all);

    println!("walkthrough:");
    for (i, s) in per_batch.iter().enumerate() {
        println!("  batch {i}: {s:?}");
    }
    println!("  merged : {merged:?}");
    println!("  one pass agrees: {}", merged == one_pass);
    assert_eq!(merged, one_pass);
    // ANCHOR_END: walkthrough
}
