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
- `apm_b90a03_exists_intermediateField` takes the fixed field of a Sylow
  subgroup. `IntermediateField.finrank_fixedField_eq_card` gives relative
  degree `p ^ n`; tower finrank arithmetic and `n,m>1` prove it is neither
  bottom nor top. This closes the complete existential conjunct.

## Remaining bridge

Transport the restricted Galois correspondence to identify literal singleton
uniqueness of degree-`p ^ n` fields with normality of the corresponding Sylow
subgroup; then apply `InfiniteGalois.normal_iff_isGalois`.
