# Proof Outline: b00J01

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves the
concrete finite-field foundation:

- exhaustive computation shows that `7` is not a cube in `ZMod 13`;
- therefore `X³ - 7` has no root over `ZMod 13`;
- the degree-three no-root criterion proves that polynomial irreducible.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b00J01.md`

## Remaining boundary

- identify an arbitrary splitting field of this irreducible cubic with the
  canonical degree-three finite Galois field and transport Frobenius;
- identify the real splitting field with `ℂ` and its automorphism group with
  `ZMod 2`;
- over `ℚ`, establish the `S₃` automorphism group and formalize the complete
  subgroup/intermediate-field correspondence, including the three non-Galois
  cubic fields.

The original skipped comment incorrectly said the cubic has one root modulo
13; the compiled computation confirms it has no roots, as required by the
informal solution and the claimed degree-three splitting field.
