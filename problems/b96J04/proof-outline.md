# Proof Outline: b96J04

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves uniformly
over every field that `X⁸+1` is the sixteenth cyclotomic polynomial, using the
prime-power geometric-sum formula. Specialized lemmas cover both `ℚ` and
`ZMod 41`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b96J04.md`

## Remaining boundary

- transport an arbitrary splitting field of `cyclotomic 16` over `ℚ` to the
  standard cyclotomic-extension automorphism group and identify its unit group
  with `ZMod 2 × ZMod 4`;
- use the finite Galois correspondence to count the three index-four/fixed
  degree-four fields and prove they are Galois;
- over `ZMod 41`, identify the splitting degree with the order of `41` modulo
  `16` and transport Frobenius to the requested order-two automorphism group.
