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
- `apm_t01J06_isOmega_unique` proves the coefficient specification uniquely
  determines the ambient form.
- `apm_t01J06_inclusionPullback_apply` gives the exact coordinate formula for
  the sphere restriction on tangent vectors, eliminating both abstract forms
  from the remaining coefficient calculation.
- `apm_t01J06_target_period_pos` proves the claimed period is nonzero.

## Remaining boundary

- Simplify the oriented coefficient of the inclusion pullback and evaluate its
  Hausdorff-measure integral as `4π/3`.
- Establish the Stokes bridge from `extDeriv eta = 0` to vanishing of the
  frozen sphere integral, yielding the nonextension result.
- Alternatively, develop direct orthogonal-projection simplification and the
  required Hausdorff sphere-coordinate moment formulas; Mathlib's box-integral
  divergence theorem does not currently connect to this integral.

## Hop 4 bridge statements

- `apm_t01J06_bridge_sphereIntegral` states the exact projection-coordinate
  and Hausdorff sphere-moment result: any specified ambient form restricts to
  a sphere form of integral `4 * Real.pi / 3`.
- `apm_t01J06_bridge_closed_extension_integral_zero` states the specialized
  Stokes theorem needed by this encoding: the restriction of a smooth closed
  ambient two-form has zero sphere integral.

The first bridge proves the numerical conjunct. The second contradicts it for
any proposed closed extension, and the already compiled projection-pullback
existential proves the final conjunct.
