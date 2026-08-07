# Proof Outline: m98A03

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m98A03.md`

## Compiled progress

- `apm_m98a03_integrable_kernel_section` proves integrability of the frozen
  Hammerstein integrand.
- `apm_m98a03_integrable_derivative_kernel_section` proves integrability of
  the proposed derivative integrand using continuity of `deriv f`.
- `apm_m98a03_derivative_kernel_norm_le` gives the uniform sup-norm estimate
  `‖K‖ * M * ‖h‖` once `deriv f` is bounded by `M`.
- `apm_m98a03_integrable_derivative_majorant` proves the associated constant
  majorant is integrable on the compact interval.

## Remaining boundary

- Package the integral as a `ContinuousMap`-valued operator.
- Localize continuity of `deriv f` to choose the bound uniformly on a
  sup-norm neighborhood and apply the parametric-integral Fréchet theorem.
- Prove continuity of the derivative map in operator norm.
