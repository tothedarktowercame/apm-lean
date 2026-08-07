# Proof Outline: t01J06

The canonical Lean attempt is `lean/Main.lean`. The product pullback clause is
now compiled directly from the alternating-map construction.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01J06.md`

## Compiled progress

- `apm_t01J06_projectionPullback_isJPullback` proves that projection pullback
  restricts to `alpha` on every slice `S² × {p}`.

## Remaining boundary

- Simplify the oriented coefficient of the inclusion pullback and evaluate its
  Hausdorff-measure integral as `4π/3`.
- Establish the Stokes bridge from `extDeriv eta = 0` to vanishing of the
  frozen sphere integral, yielding the nonextension result.
