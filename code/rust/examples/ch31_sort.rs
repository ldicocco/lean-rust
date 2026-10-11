// harness: run
//! Insertion sort and binary search in Rust, tested against the verified Lean
//! models of Chapter 31.
//!
//! Demonstrates: differential testing (the expected outputs are the table that
//! the Lean models print in `code/lean/Book/Ch31/Differential.lean`, read here
//! with `include_str!`), property-based testing against the specification
//! with a small seeded PRNG, and the difference between a specification that
//! determines the output (sorting) and one that does not (searching with
//! duplicates).
//!
//! Run with: `cargo run --example ch31_sort`

// ANCHOR: sort
/// Insertion sort, in place: the usual imperative formulation. Each new
/// element is swapped leftwards until the prefix `v[..=i]` is sorted again.
fn insertion_sort(v: &mut [i64]) {
    for i in 1..v.len() {
        let mut j = i;
        while j > 0 && v[j - 1] > v[j] {
            v.swap(j - 1, j);
            j -= 1;
        }
    }
}
// ANCHOR_END: sort

// ANCHOR: search
/// Binary search on a sorted slice: the same algorithm as the Lean model
/// `searchFrom`, with a loop instead of tail recursion. Invariant: if `x` is
/// in the slice, it is at an index in `lo..hi`.
fn binary_search(a: &[i64], x: i64) -> Option<usize> {
    let (mut lo, mut hi) = (0, a.len());
    while lo < hi {
        // Not `(lo + hi) / 2`: that sum can overflow; this cannot, since lo < hi.
        let mid = lo + (hi - lo) / 2;
        if x < a[mid] {
            hi = mid;
        } else if a[mid] < x {
            lo = mid + 1;
        } else {
            return Some(mid);
        }
    }
    None
}
// ANCHOR_END: search

// ANCHOR: read_model
/// The Lean file whose `#guard_msgs` block pins the model's outputs. Lean
/// checks that the block matches the model; this program checks that the
/// Rust implementation matches the block.
const LEAN_MODEL: &str = include_str!("../../lean/Book/Ch31/Differential.lean");

/// The lines of the expected-output table: from `info: ` to the end of the
/// doc comment.
fn expected_lines(source: &str) -> Vec<&str> {
    let start = source
        .find("info: sort")
        .expect("no table in the Lean file");
    let table = &source[start + "info: ".len()..];
    let end = table.find("-/").expect("unterminated table");
    table[..end]
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect()
}

/// Parses a Lean list of integers such as `[-2, 0, 5]`.
fn parse_list(text: &str) -> Vec<i64> {
    let inner = text.trim().trim_start_matches('[').trim_end_matches(']');
    if inner.trim().is_empty() {
        return Vec::new();
    }
    inner
        .split(',')
        .map(|n| n.trim().parse().expect("an integer"))
        .collect()
}

/// Parses `some 3` or `none`.
fn parse_option(text: &str) -> Option<usize> {
    match text.trim() {
        "none" => None,
        other => Some(other.trim_start_matches("some ").parse().expect("an index")),
    }
}
// ANCHOR_END: read_model

// ANCHOR: differential
/// Runs every line of the table through the Rust implementation.
/// Returns the number of sort and search cases checked.
fn differential_test() -> (usize, usize) {
    let (mut sorts, mut searches) = (0, 0);
    for line in expected_lines(LEAN_MODEL) {
        let (call, expected) = line.split_once(" = ").expect("`call = result`");
        if let Some(input) = call.strip_prefix("sort ") {
            let mut v = parse_list(input);
            insertion_sort(&mut v);
            assert_eq!(
                v,
                parse_list(expected),
                "differs from the Lean model: {line}"
            );
            sorts += 1;
        } else if let Some(args) = call.strip_prefix("search ") {
            let (list, key) = args.rsplit_once(' ').expect("`search list key`");
            let a = parse_list(list);
            let x: i64 = key.parse().expect("an integer key");
            let got = binary_search(&a, x);
            assert_eq!(
                got,
                parse_option(expected),
                "differs from the Lean model: {line}"
            );
            searches += 1;
        } else {
            panic!("unexpected line in the table: {line}");
        }
    }
    (sorts, searches)
}
// ANCHOR_END: differential

// ANCHOR: prng
/// SplitMix64: a tiny, seeded pseudo-random generator, so that the property
/// tests are reproducible.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A number in `lo..=hi`.
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % (hi - lo + 1) as u64) as i64
    }
}
// ANCHOR_END: prng

// ANCHOR: properties
/// Checks the two specifications on random inputs: the sort output is sorted
/// and a permutation of the input; the search result points at the key, or
/// the key is absent.
fn property_test(cases: usize) -> usize {
    let mut rng = SplitMix64(2026);
    let mut searches = 0;
    for _ in 0..cases {
        let len = rng.range(0, 20) as usize;
        let input: Vec<i64> = (0..len).map(|_| rng.range(-30, 30)).collect();

        let mut sorted = input.clone();
        insertion_sort(&mut sorted);
        assert!(
            sorted.windows(2).all(|w| w[0] <= w[1]),
            "not sorted: {sorted:?}"
        );
        // A permutation: the same multiset of elements. Sorting both sides
        // with the standard library's sort is one way to compare multisets.
        let mut reference = input.clone();
        reference.sort();
        assert_eq!(sorted, reference, "not a permutation of {input:?}");

        for x in -32..=32 {
            match binary_search(&sorted, x) {
                Some(i) => assert_eq!(sorted[i], x),
                None => assert!(!sorted.contains(&x)),
            }
            searches += 1;
        }
    }
    searches
}
// ANCHOR_END: properties

fn main() {
    // ANCHOR: main
    let (sorts, searches) = differential_test();
    println!("Lean model: {} expected results read", sorts + searches);
    println!("  sort:   {sorts} cases agree with the Lean model");
    println!("  search: {searches} cases agree with the Lean model");

    let cases = 10_000;
    let checked = property_test(cases);
    println!("property tests: {cases} random lists sorted correctly");
    println!("property tests: {checked} searches satisfy the specification");

    // With duplicates, the specification of search does not fix the index.
    let sevens = [7, 7, 7, 7];
    let ours = binary_search(&sevens, 7);
    let std_result = sevens.binary_search(&7);
    println!("search {sevens:?} 7: ours {ours:?}, std {std_result:?}");
    // ANCHOR_END: main
}
