# Proof Outline: m00A01

The Lean proof establishes both projection characterizations, the bijectivity
of the restricted complement, and its uniform positive lower bound.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m00A01.md`

## Formal progress

- The direct-sum hypotheses prove the restricted complement bijective.
- `apmRestrictedComplementCLM` packages that function as a continuous linear
  map between the two subtypes.
- `antilipschitzWith_iff_exists_mul_le_norm` has the exact positive-real
  constant and norm inequality needed by the conclusion.
- Closedness supplies `CompleteSpace M`; Mathlib's orthogonal-complement
  instance supplies completeness of the codomain subtype.
- `ContinuousLinearEquiv.ofBijective` turns the compiled bijection into a
  continuous linear equivalence. Its anti-Lipschitz estimate converts directly
  to the required ambient-space norm inequality.

There are no remaining proof obligations.
