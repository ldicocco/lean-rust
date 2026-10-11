Part I lays the foundations that everything else rests on. It starts with the
two languages of the book: what a type theory is, why we study it through Rust
and Lean together, and enough Lean to read and write the code of the coming
chapters. Then it builds the basic apparatus of the subject from the ground up:
judgments, inference rules and derivations; natural deduction, the proof system
in which every later logic is written; intuitionism, which explains what a
*constructive* proof is and why proofs can be programs; and the structural
rules, three innocent-looking rules about assumptions whose removal will
eventually give us ownership.

Every idea in this part is executed twice: implemented in Rust (a type checker,
a proof checker, a search for countermodels) and formalized in Lean, where the
first real theorems of the book are proved.
