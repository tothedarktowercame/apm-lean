import Mathlib

/-!
# APM a03J05: A cosine integral

## Statement repairs

None.

## Encoding questions

None. The improper integral over `[0, ∞)` is encoded as the Lebesgue set
integral over `Set.Ioi 0`; changing the endpoint does not affect the integral.

## Source note

The bundle has no `informal-solution.md`: `status.json` records that the
harvested file contained the a03J04 proof and was removed. The TeX statement is
therefore the sole intent source for this formal statement.
-/

open MeasureTheory Set

noncomputable section

/-- The integrand `cos(xt) / (1 + x²)`. -/
def apm_a03J05_integrand (t x : ℝ) : ℝ :=
  Real.cos (x * t) / (1 + x ^ 2)

theorem apm_a03j05 (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), apm_a03J05_integrand t x ∂volume =
      (Real.pi / 2) * Real.exp (-|t|) := by
  sorry
