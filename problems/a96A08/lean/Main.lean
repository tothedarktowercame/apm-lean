import Mathlib

/-!
# APM a96A08 — an improper sine integral

## Statement repairs

None.

The improper integral is encoded as the Lebesgue integral on `ℝ`.  The values
chosen at the removable singularities `0` and `1` do not affect that integral.
The statement includes integrability, so the displayed value is not based on
an arbitrary convention for a divergent integral.
-/

open MeasureTheory Real

noncomputable section

def apm_a96A08_integrand (x : ℝ) : ℝ :=
  Real.sin (Real.pi * x) / (x ^ 2 - x)

theorem apm_a96a08 :
    Integrable apm_a96A08_integrand volume ∧
      (∫ x : ℝ, apm_a96A08_integrand x ∂volume) = -(2 * Real.pi) := by
  sorry
