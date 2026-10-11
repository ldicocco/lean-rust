Part V returns to the structural rules of Part I and removes them, one at a
time. Without contraction, an assumption can be used at most once; without
weakening, it must be used. The resulting substructural logics, linear and
affine, are logics of resources, and the affine λ-calculus built from them is
the formal core of Rust's ownership: moves, `Copy`, `Clone` and `Drop` each find
their place in it, with a type checker in Rust and the metatheory in Lean. The
part ends with typestate, where the affine discipline turns protocols into
types.
