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

## Remaining Boundary

- Derive Euler–Lagrange from the first variation using differentiation under
  the integral, integration by parts, and the fundamental lemma.
The arc-length half is closed. The only remaining boundary is the
Euler–Lagrange implication: dominated differentiation and integration by parts
are available separately in Mathlib, but the fundamental lemma for the frozen
endpoint-zero `C¹` test-function class is not packaged.
