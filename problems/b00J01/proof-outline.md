# Proof Outline: b00J01

The canonical Lean attempt is `lean/Main.lean`. Closer hops 1–2 prove the
concrete finite-field foundation:

- exhaustive computation shows that `7` is not a cube in `ZMod 13`;
- therefore `X³ - 7` has no root over `ZMod 13`;
- the degree-three no-root criterion proves that polynomial irreducible.
- perfectness of `ZMod 13` makes the polynomial separable;
- every arbitrary splitting field from the frozen quantifier is a
  finite-dimensional Galois extension;
- its automorphism-group cardinality equals its extension degree.
- irreducibility and splitting imply that the extension degree is divisible by
  three, hence the automorphism-group cardinality is also divisible by three.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b00J01.md`

## Remaining boundary

- prove the complementary upper bound that the irreducible cubic's root field
  already contains all three roots, then identify the arbitrary splitting
  field with the canonical degree-three Galois field and transport Frobenius;
- identify the real splitting field with `ℂ` and its automorphism group with
  `ZMod 2`;
- over `ℚ`, establish the `S₃` automorphism group and formalize the complete
  subgroup/intermediate-field correspondence, including the three non-Galois
  cubic fields.

The original skipped comment incorrectly said the cubic has one root modulo
13; the compiled computation confirms it has no roots, as required by the
informal solution and the claimed degree-three splitting field.
