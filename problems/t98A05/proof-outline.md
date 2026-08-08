# Proof Outline: t98A05

The canonical Lean artifact is a compiling honest partial with one remaining
`sorry` on the main theorem.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t98A05.md`

## Compiled progress

- `apm_t98a05_wedgeEval_eq_zero` proves the full wedge-vanishing conjunct by
  expanding the specified forms and polynomial normalization.
- `apm_t98a05_circleClosed_of_extDeriv_formula` proves circle closedness from
  the theorem's displayed formula for `extDeriv alpha`; tangent vectors to the
  unit circle have zero two-dimensional determinant.

## Remaining boundary

- Compute the three exterior derivatives from the pointwise coordinate
  specifications. Mathlib's `extDeriv_apply` reduces this to explicit Frechet
  derivatives of alternating-map-valued functions, but those bundles and
  derivative proofs are not packaged.
- Evaluate the resulting constant two-form on the triangular parameter domain.
- Prove nonexactness by a differentiable circle parametrization and the
  nonzero period of the restricted one-form.
