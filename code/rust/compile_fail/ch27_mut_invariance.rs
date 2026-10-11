// harness: compile-fail E0597
//! The classic unsound program that the invariance of `&mut T` in `T` rejects:
//! if `&mut &'static str` could be used as `&mut &'short str`, a short-lived
//! reference could be written into a `'static` slot.

// ANCHOR: overwrite
fn overwrite<T>(dst: &mut T, src: T) {
    *dst = src;
}

pub fn evil() {
    let mut s: &'static str = "static data";
    {
        let local = String::from("short-lived");
        overwrite(&mut s, &local);
    }
    println!("{s}");
}
// ANCHOR_END: overwrite
