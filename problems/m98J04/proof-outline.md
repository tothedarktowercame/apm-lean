# Proof Outline: m98J04

The canonical Lean attempt is `lean/Main.lean`. It proves admissibility and
the complete endpoint-length calculation for the straight line.

- `apm_m98J04_deriv_line` computes the constant slope.
- `apm_m98J04_arcLength_line` evaluates the custom interval integral.
- `apm_m98J04_arcLength_line_eq_sqrt` proves that value equals the Euclidean
  endpoint distance `sqrt ((b-a)² + (β-α)²)`.
- `apm_m98J04_integral_deriv_eq_sub` compiles the `C¹` endpoint FTC bridge.
- `apm_m98J04_integral_complex_tangent` encodes the graph tangent as
  `1 + y' * I`; the complex norm is the arc-length integrand, so the integral
  triangle inequality proves global minimality of the line.
- The theorem proves the line is globally `C¹` and has the required endpoints.
- `apm_m98J04_eq_zero_on_Ioo_of_ae` upgrades an almost-everywhere zero
  continuous Euler residual to pointwise zero on the open interval.

## Remaining Boundary

- Derive the integral Euler residual from the first variation using
  differentiation under the integral and integration by parts.
- Convert the interval identity to the compactly-supported whole-space test
  hypothesis of `ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
The arc-length half is closed. Hop 4 states the remaining Euler--Lagrange
implication precisely as
`apm_m98J04_bridge_stationary_imp_eulerLagrange`. Its proof must differentiate
the frozen first variation, integrate the momentum term by parts, convert to
whole-space compactly supported smooth tests, invoke
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`, and finish with the compiled
continuous pointwise upgrade. The bridge is intentionally unproved, and the
main theorem is unchanged.
