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
- `apm_m93J03_affineTrig` and `apm_m93J03_residual` package the exact
  two-dimensional reduced equation.
- `apm_m93J03_isSolution_affineTrig_of_residual_eq_zero` reconstructs a
  genuine continuous solution of the original equation from any residual
  zero.

## Remaining boundary

- prove the exact strict derivative statement recorded at the sorry boundary:
  its action is `h ↦ ((1+π)*h.2.1, (1-π)*h.2.2)`. The available dominated
  parameter-integral theorem supplies only `HasFDerivAt`, whereas the chosen
  product-domain theorem requires `HasStrictFDerivAt`;
- apply the product-domain implicit-function theorem to the now-explicit
  residual;
- convert its neighborhood existence and uniqueness into fixed scalar radii
  `δ` and `η`; use the compiled affine-trigonometric reduction to lift the
  coefficient-pair uniqueness back to arbitrary function-valued solutions.
