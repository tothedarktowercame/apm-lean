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
- The main theorem now invokes `apm_b94J03_finiteField_conclusion` directly;
  its sole sorry is restricted to the paired characteristic-zero clauses.

## Hop 4 bridge contracts

- `apm_b94J03_bridge_complex_model` states that `ℂ` is the splitting field of
  the real cubic and that its real automorphism group is `ZMod 2`.
  `IsSplittingField.algEquiv` and `AlgEquiv.autCongr` provide the transport to
  an arbitrary real splitting field.
- `apm_b94J03_bridge_rational_conclusion` states the rational degree-six and
  `S₃` result for an arbitrary splitting field, encapsulating the irreducible
  cubic, discriminant, root action, and surjectivity calculation.

Both declarations are intentionally unproved. The finite-field case remains
complete, and the main theorem is unchanged.
