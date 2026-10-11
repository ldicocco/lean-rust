// harness: compile-fail E0382
//! ¬(A ∨ B) → ¬A ∧ ¬B uses its hypothesis twice. Without `Clone`, Rust
//! rejects the proof: the refutation `n` is moved into the first closure.

enum Void {}

enum Either<A, B> {
    Left(A),
    Right(B),
}

// ANCHOR: de_morgan
fn de_morgan_or<A, B, N>(n: N) -> (impl FnOnce(A) -> Void, impl FnOnce(B) -> Void)
where
    N: FnOnce(Either<A, B>) -> Void,
{
    (move |a| n(Either::Left(a)), move |b| n(Either::Right(b)))
}
// ANCHOR_END: de_morgan
