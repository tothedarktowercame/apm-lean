# Proof Outline: b97J04

The canonical Lean attempt compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97J04.md`

## Compiled progress

- `apm_b97j04_additive_exists` constructs the commuting additive
  Jordan--Chevalley decomposition using Mathlib's polynomial-in-`T` theorem.
- `apm_b97j04_additive_unique` proves uniqueness by translating the frozen
  predicate to Mathlib's uniqueness theorem.
- `apm_b97j04_eigenspace_subset_generalized` proves that every eigenvector of
  the semisimple part lies in the frozen positive-power generalized
  eigenspace of the original operator.
- `apm_b97j04_mapsTo_generalizedEigenspace` proves that both additive
  components preserve every generalized eigenspace of `T`, by commuting them
  with all powers of `T-λ`.

## Remaining bridge

Use the compiled `MapsTo` facts to restrict the two Jordan--Chevalley
components to `T.maxGenEigenspace λ`, and apply uniqueness to prove the reverse
generalized-eigenspace inclusion. Then use root multiplicities for
characteristic-polynomial equality and derive the unique multiplicative
decomposition of a linear equivalence.
