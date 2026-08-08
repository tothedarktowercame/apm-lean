import Mathlib

/-!
# APM a94J06 — a conjugate contour integral on the unit circle

## Statement repairs

None.

The theorem states all three cases. For a point on the circle, the ordinary
contour integral is not defined because the parametrized integrand is not
integrable; no principal-value convention is silently introduced.
-/

open Complex Real

noncomputable section

def apm_a94J06_integrand (z ζ : ℂ) : ℂ :=
  starRingEnd ℂ ζ / (ζ - z)

theorem apm_a94j06 (z : ℂ) :
    (‖z‖ < 1 →
      (∮ ζ in C(0, 1), apm_a94J06_integrand z ζ) = 0) ∧
    (1 < ‖z‖ →
      (∮ ζ in C(0, 1), apm_a94J06_integrand z ζ) =
        -(2 * Real.pi * Complex.I) / z) ∧
    (‖z‖ = 1 →
      ¬CircleIntegrable (apm_a94J06_integrand z) 0 1) := by
  sorry
