# Proof Outline: t01A06

The theorem is fully proved in `lean/Main.lean` with no sorries.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01A06.md`

## Proof structure

- Expand the pulled-back two-form into cosine moments and evaluate the inner
  integral using `integral_cos_sq` and `integral_cos_pow_three`; the outer
  sine-square integral gives `2 * π² * R * r²`.
- Apply
  `convex_univ.exists_forall_hasFDerivAt_of_fderiv_symmetric` to obtain a
  global potential for any ambient closed one-form.
- Compose the potential with the smooth periodic loop. The line-integral
  integrand is the derivative of this composite, so
  `intervalIntegral.integral_deriv_eq_sub` and periodicity make the integral
  zero.

## Audit

- `lake env lean problems/t01A06/lean/Main.lean`: exit 0.
- Main theorem has no `sorryAx` dependency.
