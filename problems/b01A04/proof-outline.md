# Proof Outline: b01A04

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves
`apm_b01A04_isGaloisGroup_of_mulEquiv`: once a concrete group model is
realized, realizability transports to any isomorphic group. This isolates away
the eventual `A₃`, cyclotomic-unit, and additive/multiplicative model changes.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b01A04.md`

## Remaining boundary

- construct a cyclic cubic Galois extension, either as the real cubic subfield
  of `ℚ(ζ₇)` or as the splitting field of an explicit irreducible cubic with
  square discriminant;
- identify its automorphism group with an order-three concrete group and use
  the compiled transport helper;
- construct two linearly disjoint cyclic cubic extensions and formalize the
  restriction isomorphism from their compositum's Galois group to the product.
