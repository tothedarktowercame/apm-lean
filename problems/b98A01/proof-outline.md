# Proof Outline: b98A01

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
The finite Sylow-count and normalizer-cardinality arithmetic is now complete.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b98A01.md`

## Compiled progress

- A nontrivial divisor of `42` congruent to one modulo five is `6` or `21`.
- If that count times a normalizer cardinality is `210`, the normalizer has
  cardinality `10` or `35`.
- Every order-five subgroup is explicitly promoted to a Sylow subgroup and
  has index `42`.
- For a nonnormal order-five subgroup, the normalizer is proved to have
  cardinality `10` or `35` using the Sylow count and normalizer-index formula.
- `apm_b98a01_coset_core_action` constructs the required action on `Fin n`,
  identifies its kernel with the normal core, and proves the universal
  property. This closes part (a), which is wired into the main theorem along
  with the normalizer alternative.

## Remaining bridge

Complete the index-six core argument, the exclusivity/refinement clauses, and the
equivalence between an order-35 subgroup and a normal order-seven subgroup.
