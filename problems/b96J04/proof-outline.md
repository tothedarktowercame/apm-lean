# Proof Outline: b96J04

The canonical Lean attempt is `lean/Main.lean`. Closer hop 1 proves uniformly
over every field that `X⁸+1` is the sixteenth cyclotomic polynomial, using the
prime-power geometric-sum formula. Specialized lemmas cover both `ℚ` and
`ZMod 41`.

Closer hop 2 proves the concrete arithmetic facts needed after the missing
transport: `apm_b96J04_orderOf_41_mod_16` establishes that `41` has order two
in `ZMod 16`, while `apm_b96J04_card_units_mod_16` establishes that
`(ZMod 16)ˣ` has eight elements. The former uses `orderOf_eq_prime`; the latter
reduces `Nat.card` to a computable `Fintype.card` calculation.

Closer hop 3 proves `apm_b96J04_aut_equiv_units_of_isCyclotomic`. Once `K` is
recognized as an `IsCyclotomicExtension {16} ℚ K`, Mathlib's
`IsCyclotomicExtension.Rat.galEquivZMod` directly identifies its automorphism
group with `(ZMod 16)ˣ`; transporting hop 2's calculation also gives
automorphism-group cardinality eight.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b96J04.md`

## Remaining boundary

- construct `IsCyclotomicExtension {16} ℚ K` from the arbitrary splitting-
  field instance, then identify `(ZMod 16)ˣ` with `ZMod 2 × ZMod 4`;
- use the finite Galois correspondence to count the three index-four/fixed
  degree-four fields and prove they are Galois;
- over `ZMod 41`, identify the splitting degree with the order of `41` modulo
  `16` (whose value two is now compiled) and transport Frobenius to the
  requested order-two automorphism group.
