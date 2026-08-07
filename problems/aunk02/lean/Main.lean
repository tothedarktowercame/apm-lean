import Mathlib

/-!
# APM aunk02

## Statement repairs

None. The standard complex-analysis meaning of “region” as a connected open
set is made explicit.

## Encoding questions

None. Holomorphicity on the region is `DifferentiableOn ℂ`, and a complex
value is real exactly when its imaginary part vanishes.
-/

theorem apm_aunk02 (Ω : Set ℂ) (f : ℂ → ℂ)
    (hΩopen : IsOpen Ω) (hΩconn : IsConnected Ω)
    (hf : DifferentiableOn ℂ f Ω)
    (hdisk : ∃ z₀ : ℂ, ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ Ω ∧
      ∀ z ∈ Metric.ball z₀ r, (f z).im = 0) :
    ∀ z ∈ Ω, (f z).im = 0 := by
  sorry
