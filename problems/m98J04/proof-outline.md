# Proof Outline: m98J04

The canonical Lean attempt is `lean/Main.lean`. It proves admissibility and
the complete endpoint-length calculation for the straight line.

- `apm_m98J04_deriv_line` computes the constant slope.
- `apm_m98J04_arcLength_line` evaluates the custom interval integral.
- `apm_m98J04_arcLength_line_eq_sqrt` proves that value equals the Euclidean
  endpoint distance `sqrt ((b-a)² + (β-α)²)`.
- The theorem proves the line is globally `C¹` and has the required endpoints.

## Remaining Boundary

- Derive Euler–Lagrange from the first variation using differentiation under
  the integral, integration by parts, and the fundamental lemma.
- Prove every admissible graph has length at least its endpoint distance by
  rewriting the integrand as the norm of `(1, deriv y)` and applying the
  integral triangle inequality plus the fundamental theorem of calculus.
