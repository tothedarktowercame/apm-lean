# Proof Outline: m00A01

The canonical Lean attempt proves both projection characterizations and the
bijectivity of the restricted complement. One sorry remains for the uniform
positive lower bound.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m00A01.md`

## Formal progress

- The direct-sum hypotheses prove the restricted complement bijective.
- `apmRestrictedComplementCLM` packages that function as a continuous linear
  map between the two subtypes.
- `antilipschitzWith_iff_exists_mul_le_norm` has the exact positive-real
  constant and norm inequality needed by the conclusion.

## Remaining bridge

Install the closed-subspace completeness instances in the form expected by
`ContinuousLinearEquiv.ofBijective`, build the equivalence from the compiled
map and bijectivity proof, and pass its antilipschitz estimate through
`antilipschitzWith_iff_exists_mul_le_norm`.
