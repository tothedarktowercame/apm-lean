# Proof Outline: m93J03

The frozen theorem has a partial Lean development with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J03.md`

## Compiled progress

- `apm_m93J03_isSmall_mono` proves monotonicity in the uniform radius.
- `apm_m93J03_zero_isSmall` establishes the trivial branch's radius bound.
- `apm_m93J03_solution_eq_affine_trig` proves every solution has the exact
  form `ε + a sin t + b cos t` on the frozen interval, with `a` and `b` given
  by the separated cosine and sine integrals.

## Remaining boundary

- differentiate the resulting two parameterized integrals and compute the
  partial Jacobian at zero;
- apply the product-domain implicit-function theorem;
- convert its neighborhood existence and uniqueness into fixed scalar radii
  `δ` and `η`; use the compiled affine-trigonometric reduction to lift the
  coefficient-pair uniqueness back to arbitrary function-valued solutions.
