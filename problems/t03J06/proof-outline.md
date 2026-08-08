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

## Remaining boundary

The local `extDeriv` computation must be bundled to prove smoothness,
nonclosedness, and nonexactness via `extDeriv_extDeriv`. For the final period,
the intended capping argument requires a Stokes/divergence theorem compatible
with these parametrized surface integrals. The available theorem treats boxes;
the alternative direct proof needs disk symmetry and integrability estimates
for the hemisphere's square-root boundary singularity.
