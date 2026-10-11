//! A tiny seeded pseudo-random number generator (SplitMix64), so that the
//! property tests need no external crate and every run is reproducible.

// ANCHOR: rng
/// SplitMix64: a 64-bit state advanced by a constant, then scrambled.
/// Not for cryptography; good enough to drive a test generator.
#[derive(Clone, Debug)]
pub struct Rng {
    state: u64,
}

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng { state: seed }
    }

    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A number in `0..n` (with a negligible bias for small `n`).
    pub fn below(&mut self, n: usize) -> usize {
        assert!(n > 0, "below(0)");
        (self.next_u64() % n as u64) as usize
    }

    /// An element of a non-empty slice.
    pub fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }
}
// ANCHOR_END: rng

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_seed_same_sequence() {
        let mut a = Rng::new(42);
        let mut b = Rng::new(42);
        for _ in 0..100 {
            assert_eq!(a.next_u64(), b.next_u64());
        }
    }

    #[test]
    fn below_stays_in_range_and_hits_every_value() {
        let mut rng = Rng::new(7);
        let mut seen = [false; 5];
        for _ in 0..1000 {
            let k = rng.below(5);
            seen[k] = true;
        }
        assert!(seen.iter().all(|&s| s));
    }
}
