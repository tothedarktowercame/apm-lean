# Proof Outline: t03J06

The local surface-form algebra is now formalized and compiles.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t03J06.md`

## Compiled steps

- `apm_t03J06_isOmega_unique` shows the coordinate predicate uniquely fixes
  the supplied alternating form.
- `apm_t03J06_vec3_apply` provides coordinate reduction for the custom vector.
- `apm_t03J06_cylinder_integrand` evaluates the form on the cylinder tangent
  pair.
- `apm_t03J06_hemisphere_integrand` evaluates it on the hemisphere graph
  tangent pair and exposes the boundary quotient terms explicitly.
- `apm_t03J06_extDeriv_ne_zero_of_eval_three` derives nonclosedness directly
  from the displayed value `3`.
- `apm_t03J06_not_exact_of_extDeriv_eval_three` applies Mathlib's `d² = 0`
  theorem to show that the same displayed value rules out every smooth
  primitive. Thus the second main conjunct implies the third and fourth.

## Remaining boundary

The local `extDeriv` computation and smoothness proof remain to be bundled;
nonclosedness and nonexactness then follow from the compiled helpers. For the final period,
the intended capping argument requires a Stokes/divergence theorem compatible
with these parametrized surface integrals. The available theorem treats boxes;
the alternative direct proof needs disk symmetry and integrability estimates
for the hemisphere's square-root boundary singularity.
