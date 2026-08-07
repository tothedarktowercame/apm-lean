import Mathlib

/-!
# APM a96J03

## Statement repairs

None.

## Encoding questions

None. Membership in `L¹(ℝ, μ)` is expressed for the given representative by
`MeasureTheory.Integrable f volume`, and the displayed limit is encoded
directly with the neighborhood filter at zero.
-/

open MeasureTheory Filter

theorem apm_a96j03 (f : ℝ → ℝ) (hf : Integrable f volume) :
    Tendsto
      (fun t : ℝ => ∫ x : ℝ, |f (x - t) - f x|)
      (nhds 0) (nhds 0) := by
  sorry
