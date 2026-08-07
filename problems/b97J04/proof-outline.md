# Proof Outline: b97J04

The canonical Lean attempt compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97J04.md`

## Compiled progress

- `apm_b97j04_additive_exists` constructs the commuting additive
  Jordan--Chevalley decomposition using Mathlib's polynomial-in-`T` theorem.
- `apm_b97j04_additive_unique` proves uniqueness by translating the frozen
  predicate to Mathlib's uniqueness theorem.

## Remaining bridge

Prove preservation of characteristic polynomial, identify the custom
existential-power generalized eigenspace with the semisimple-part eigenspace,
and derive the unique multiplicative decomposition of a linear equivalence.
