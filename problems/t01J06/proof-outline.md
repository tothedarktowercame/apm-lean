# Proof Outline: t01J06

The canonical Lean attempt is `lean/Main.lean`. The product pullback clause is
now compiled directly from the alternating-map construction.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01J06.md`

## Compiled progress

- `apm_t01J06_projectionPullback_isJPullback` proves that projection pullback
  restricts to `alpha` on every slice `S² × {p}`.
- `apm_t01J06_exists_projectionPullback` packages the actual existential
  required by the theorem's final conjunct.
- `apm_t01J06_inclusionPullback_unique` proves the restricted sphere form is
  uniquely determined by its ambient form.

## Remaining boundary

- Simplify the oriented coefficient of the inclusion pullback and evaluate its
  Hausdorff-measure integral as `4π/3`.
- Establish the Stokes bridge from `extDeriv eta = 0` to vanishing of the
  frozen sphere integral, yielding the nonextension result.
- Alternatively, develop direct orthogonal-projection simplification and the
  required Hausdorff sphere-coordinate moment formulas; Mathlib's box-integral
  divergence theorem does not currently connect to this integral.
