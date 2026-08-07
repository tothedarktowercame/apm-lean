# Proof Outline: b90A03

The frozen theorem is elaborated in `lean/Main.lean`. The current partial
formalization proves the exact prime factorization of the extension degree and
deduces that every Sylow `p`-subgroup of `Gal(F/K)` has cardinality `p ^ n`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b90A03.md`

## Compiled progress

- `apm_b90a03_factorization` computes the `p`-factorization exponent.
- `apm_b90a03_sylow_card` combines it with the finite Galois cardinality
  theorem and `Sylow.card_eq_multiplicity`.

## Remaining bridge

Construct the fixed field of a Sylow subgroup, prove it is proper, and transport
the restricted Galois correspondence to identify literal singleton uniqueness
of degree-`p ^ n` fields with normality of the corresponding Sylow subgroup;
then apply `InfiniteGalois.normal_iff_isGalois`.
