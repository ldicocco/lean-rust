// harness: compile-fail E0308
//! A (2 × 3) matrix times a (2 × 3) matrix: the inner dimensions disagree.
use std::ops::Mul;

pub struct Matrix<const R: usize, const C: usize> {
    pub rows: [[i64; C]; R],
}

impl<const R: usize, const C: usize, const K: usize> Mul<Matrix<C, K>>
    for Matrix<R, C>
{
    type Output = Matrix<R, K>;
    fn mul(self, rhs: Matrix<C, K>) -> Matrix<R, K> {
        todo!()
    }
}

// ANCHOR: mismatch
pub fn product(a: Matrix<2, 3>, b: Matrix<2, 3>) {
    let _c = a * b;
}
// ANCHOR_END: mismatch
