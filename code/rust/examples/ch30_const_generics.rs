// harness: run
//! Const generics: values inside types.
//!
//! Demonstrates: arrays `[T; N]` and functions generic over their length, a
//! `Matrix<R, C>` whose multiplication type-checks only when the inner
//! dimensions agree, an identity that exists only for square matrices, a
//! compile-time assertion on a const parameter, the bridge from run-time data
//! to a static shape (`TryFrom`), and slices as dependent pairs (a length
//! stored next to the pointer).
//!
//! Run with: `cargo run --example ch30_const_generics`

use std::mem::size_of;
use std::ops::Mul;

// ANCHOR: dot
/// The dot product of two arrays of the same length `N`. The length is a
/// const parameter: a value that is part of the type, inferred at each call.
fn dot<const N: usize>(a: [i64; N], b: [i64; N]) -> i64 {
    let mut sum = 0;
    for i in 0..N {
        sum += a[i] * b[i];
    }
    sum
}
// ANCHOR_END: dot

// ANCHOR: matrix
/// An `R × C` matrix of integers. `R` and `C` are values of type `usize`, and
/// they are part of the type: `Matrix<2, 3>` and `Matrix<3, 2>` are different
/// types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Matrix<const R: usize, const C: usize> {
    rows: [[i64; C]; R],
}

impl<const R: usize, const C: usize> Matrix<R, C> {
    fn new(rows: [[i64; C]; R]) -> Self {
        Matrix { rows }
    }

    /// Rows become columns: an `R × C` matrix becomes a `C × R` matrix.
    fn transpose(&self) -> Matrix<C, R> {
        let mut out = [[0; R]; C];
        for i in 0..R {
            for j in 0..C {
                out[j][i] = self.rows[i][j];
            }
        }
        Matrix { rows: out }
    }
}
// ANCHOR_END: matrix

// ANCHOR: mul
/// `(R × C) * (C × K) = (R × K)`. The left operand's column count and the
/// right operand's row count are the *same* parameter `C`, so a product with
/// mismatched inner dimensions has no implementation to use.
impl<const R: usize, const C: usize, const K: usize> Mul<Matrix<C, K>>
    for Matrix<R, C>
{
    type Output = Matrix<R, K>;

    fn mul(self, rhs: Matrix<C, K>) -> Matrix<R, K> {
        let mut out = [[0; K]; R];
        for i in 0..R {
            for k in 0..K {
                for j in 0..C {
                    out[i][k] += self.rows[i][j] * rhs.rows[j][k];
                }
            }
        }
        Matrix { rows: out }
    }
}
// ANCHOR_END: mul

// ANCHOR: identity
/// The identity exists only for square matrices: this `impl` block is for
/// `Matrix<N, N>`, so `Matrix::<2, 3>::identity()` does not exist.
impl<const N: usize> Matrix<N, N> {
    fn identity() -> Self {
        let mut rows = [[0; N]; N];
        for (i, row) in rows.iter_mut().enumerate() {
            row[i] = 1;
        }
        Matrix { rows }
    }
}
// ANCHOR_END: identity

// ANCHOR: first
/// The first element of a non-empty array. Stable Rust has no way to write
/// `where N > 0` in the signature; the inline `const` block is evaluated when
/// the function is instantiated with a concrete `N`, and a failed assertion
/// stops the compilation.
fn first<T, const N: usize>(items: &[T; N]) -> &T {
    const { assert!(N > 0, "first() needs a non-empty array") };
    &items[0]
}
// ANCHOR_END: first

// ANCHOR: vstack
/// Stable Rust cannot write the result type `Matrix<{ R1 + R2 }, C>`. The
/// workaround: let the caller name the result size `R`, and check `R == R1 + R2`
/// in a `const` block when the function is instantiated.
fn vstack<const R1: usize, const R2: usize, const R: usize, const C: usize>(
    top: Matrix<R1, C>,
    bottom: Matrix<R2, C>,
) -> Matrix<R, C> {
    const { assert!(R == R1 + R2, "vstack: R must be R1 + R2") };
    let mut rows = [[0; C]; R];
    rows[..R1].copy_from_slice(&top.rows);
    rows[R1..].copy_from_slice(&bottom.rows);
    Matrix { rows }
}
// ANCHOR_END: vstack

// ANCHOR: try_from
/// From run-time data to a static shape. The number of values on the line is
/// known only at run time; `try_from` checks it once, and from then on the
/// length is part of the type.
fn parse_row<const N: usize>(line: &str) -> Result<[i64; N], String> {
    let mut values = Vec::new();
    for word in line.split_whitespace() {
        let value: i64 = word
            .parse()
            .map_err(|_| format!("not a number: {word:?}"))?;
        values.push(value);
    }
    let found = values.len();
    <[i64; N]>::try_from(values)
        .map_err(|_| format!("expected {N} numbers, found {found}"))
}
// ANCHOR_END: try_from

fn main() {
    // ANCHOR: main_dot
    println!("dot([1, 2, 3], [4, 5, 6]) = {}", dot([1, 2, 3], [4, 5, 6]));
    // ANCHOR_END: main_dot

    // ANCHOR: main_matrix
    let a = Matrix::new([[1, 2, 3], [4, 5, 6]]); // Matrix<2, 3>
    let b = Matrix::new([[7, 8], [9, 10], [11, 12]]); // Matrix<3, 2>
    let ab: Matrix<2, 2> = a * b;
    let ba: Matrix<3, 3> = b * a;
    println!("a * b       = {:?}", ab.rows);
    println!("b * a       = {:?}", ba.rows);
    println!("transpose a = {:?}", a.transpose().rows);
    assert_eq!(Matrix::<2, 2>::identity() * a, a);
    assert_eq!(a * Matrix::<3, 3>::identity(), a);
    assert_eq!((a * b).transpose(), b.transpose() * a.transpose());
    println!("identity laws and (a * b)^T = b^T * a^T hold");
    // ANCHOR_END: main_matrix

    // ANCHOR: main_vstack
    let stacked: Matrix<4, 3> = vstack(a, a);
    println!("vstack(a, a) = {:?}", stacked.rows);
    // ANCHOR_END: main_vstack

    // ANCHOR: main_first
    println!("first(&[7, 8, 9]) = {}", first(&[7, 8, 9]));
    // ANCHOR_END: main_first

    // ANCHOR: main_parse
    let row: Result<[i64; 3], String> = parse_row("1 2 3");
    println!("parse_row::<3>(\"1 2 3\") = {row:?}");
    let short: Result<[i64; 3], String> = parse_row("1 2");
    println!("parse_row::<3>(\"1 2\")   = {short:?}");
    if let Ok(r) = row {
        // From here on the length is static: `dot` accepts only another [i64; 3].
        println!("dot(row, row) = {}", dot(r, r));
    }
    // ANCHOR_END: main_parse

    // ANCHOR: main_sigma
    // A slice is a dependent pair: a length, and that many elements. Coercing
    // `&[i64; 3]` to `&[i64]` moves the length from the type into the value,
    // so the reference doubles in size.
    let array: [i64; 3] = [1, 2, 3];
    let slice: &[i64] = &array;
    println!(
        "size_of::<&[i64; 3]>() = {}, size_of::<&[i64]>() = {}, slice.len() = {}",
        size_of::<&[i64; 3]>(),
        size_of::<&[i64]>(),
        slice.len()
    );
    // ANCHOR_END: main_sigma
}
