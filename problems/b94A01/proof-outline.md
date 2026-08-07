# Proof Outline: b94A01

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
It proves the Sylow cardinalities, normality of the subgroup of order five,
the internal complement conditions, and the resulting semidirect-product
decomposition.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b94A01.md`

## Compiled progress

- `apm_b94a01_complement` obtains disjointness, generation, and the concrete
  Mathlib semidirect-product equivalence from cardinality and normality.
- The main proof computes `Nat.card (MulAut P) = 4` from cyclicity of `P`.
- `apm_b94a01_enumerate_mulAut` converts that cardinality into an actual
  injective exhaustive map `Fin 4 → MulAut P` using
  `Fintype.equivFinOfCardEq`. The main proof discharges the corresponding
  first two obligations on `Ψ` with this helper.

## Remaining bridge

Reindex/identify the enumeration with the exact requested power formula via
`IsCyclic.mulAutMulEquiv`, classify maps from `Q`, and show that
noncommutativity forces conjugation by `y` to be inversion. The final two
multiplication identities then reduce to cyclic exponent arithmetic.
