// harness: compile-fail E0770
//! Two things stable const generics cannot do: compute with a const parameter
//! inside a type, and let the type of one const parameter depend on another.

pub struct Matrix<const R: usize, const C: usize> {
    pub rows: [[i64; C]; R],
}

// ANCHOR: vstack
/// Stack `top` (R1 rows) on `bottom` (R2 rows): the result has R1 + R2 rows.
pub fn vstack<const R1: usize, const R2: usize, const C: usize>(
    top: Matrix<R1, C>,
    bottom: Matrix<R2, C>,
) -> Matrix<{ R1 + R2 }, C> {
    todo!()
}
// ANCHOR_END: vstack

// ANCHOR: dependent_param
/// A tensor shape: `N` dimensions, and an array of exactly `N` extents.
pub struct Shape<const N: usize, const DIMS: [usize; N]>;
// ANCHOR_END: dependent_param
