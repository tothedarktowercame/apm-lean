# Proof Outline: m98A03

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m98A03.md`

## Compiled progress

- `apm_m98a03_integrable_kernel_section` proves integrability of the frozen
  Hammerstein integrand.
- `apm_m98a03_integrable_derivative_kernel_section` proves integrability of
  the proposed derivative integrand using continuity of `deriv f`.

## Remaining boundary

- Package the integral as a `ContinuousMap`-valued operator.
- Establish a uniform integrable derivative bound on sup-norm neighborhoods
  and apply the parametric-integral Fréchet theorem.
- Prove continuity of the derivative map in operator norm.
