import Mathlib

/-!
# APM a97J06: A cosine transform

## Statement repairs

None.

## Encoding questions

None. The improper integral over `[0, ∞)` is represented by the Lebesgue set
integral over `Set.Ioi 0`; the omitted endpoint is a null set.
-/

open MeasureTheory Set

noncomputable section

/-- The integrand `cos(tx) / (x² + 4)`. -/
def apm_a97J06_integrand (t x : ℝ) : ℝ :=
  Real.cos (t * x) / (x ^ 2 + 4)

theorem apm_a97j06 (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), apm_a97J06_integrand t x ∂volume =
      (Real.pi / 4) * Real.exp (-2 * |t|) := by
  sorry
