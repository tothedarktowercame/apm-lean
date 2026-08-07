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
- `apm_b94J03_primitiveRoot_two_mod7` proves that `2 : ZMod 7` is a
  primitive cube root of unity.
- `apm_b94J03_finiteField_conclusion` applies
  `finrank_of_isSplittingField_X_pow_sub_C` and `autEquivZmod`, closing the
  entire finite-field conjunct: degree three, cardinality 343, and the exact
  bundled cyclic Galois-group equivalence.

## Remaining bridge

Realize the rational splitting field and its `S₃` action, and identify the
real splitting field with `ℂ` and its Galois group with `ZMod 2`. The
finite-field case is complete.
