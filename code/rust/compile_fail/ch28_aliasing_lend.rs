// harness: compile-fail E0382
//! Derivation II written with the calculus's borrow rule as a Rust function:
//! the owner `v` is moved into `lend` and also needed inside the body.

fn lend<T, S>(owner: Box<T>, body: impl for<'a> FnOnce(&'a T) -> S) -> (Box<T>, S) {
    let result = body(&*owner);
    (owner, result)
}

fn lend_mut<T, S>(
    mut owner: Box<T>,
    body: impl for<'a> FnOnce(&'a mut T) -> S,
) -> (Box<T>, S) {
    let result = body(&mut *owner);
    (owner, result)
}

// ANCHOR: aliasing_lend
pub fn aliasing_lend(v: Box<Vec<i32>>) -> i32 {
    let (_v, first) = lend(v, |f| {
        let (_v2, ()) = lend_mut(v, |m| m.push(4));
        f[0]
    });
    first
}
// ANCHOR_END: aliasing_lend
