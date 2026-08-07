# Proof Outline: b94J03

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
The finite-field polynomial is proved irreducible, and the cardinality
consequences of the target degree are packaged as reusable lemmas.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b94J03.md`

## Compiled progress

- `X³ - 3` is irreducible over `ZMod 7`.
- A finite degree-three extension of `ZMod 7` has cardinality `343`.
- Its Galois automorphism group has cardinality three.

## Remaining bridge

Compute each abstract splitting-field degree by realizing the required roots
and roots of unity. Then upgrade automorphism-group cardinalities to the
specific bundled equivalences with `S₃`, `ZMod 2`, and `ZMod 3`.
