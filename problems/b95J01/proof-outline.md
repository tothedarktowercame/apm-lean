# Proof Outline: b95J01

The Lean proof is complete in `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b95J01.md`

## Formal proof

- For each `g`, pull `H` back along `zpowersHom` to an additive subgroup of
  `ℤ`. Cyclicity gives a positive generator `k`, whose divisibility
  characterization proves minimality and divisibility of every integer
  exponent landing in `H`.
- When `H` is normal, `H.pow_index_mem g` puts the index exponent in `H`, so
  the generator divides `H.index`.
- The explicit `S₃` subgroup is computed using the order-two transposition,
  subgroup cardinality, and kernel-checked finite decisions. Conjugation proves
  non-normality, its index is three, and the second transposition supplies the
  requested exponent-two counterexample.
