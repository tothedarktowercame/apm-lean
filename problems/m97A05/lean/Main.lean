import Mathlib.Analysis.Distribution.TemperedDistribution

/-! # APM m97A05: the distribution carried by the line `y = -x`

## Statement repairs

The displayed domain is repaired from `ℝ` to `ℝ²`, since the test function is
evaluated at `(s,-s)`.  Complex-valued Schwartz functions and Mathlib's Fourier
normalization are used, making this a tempered-distribution formulation.

## Encoding questions

The requested distribution is characterized by its action on every Schwartz
test function.  Coordinate derivatives are the existing directional derivative
operation on tempered distributions.
-/

open SchwartzMap MeasureTheory
open scoped SchwartzMap LineDeriv

theorem apm_m97a05 :
    ∃ T : 𝓢'(ℝ × ℝ, ℂ),
      (∀ φ : 𝓢(ℝ × ℝ, ℂ), T φ = ∫ s : ℝ, φ (s, -s)) ∧
      ∂_{((1, 0) : ℝ × ℝ)} T = ∂_{((0, 1) : ℝ × ℝ)} T ∧
      ∂_{((1, 0) : ℝ × ℝ)} (∂_{((1, 0) : ℝ × ℝ)} T) =
        ∂_{((0, 1) : ℝ × ℝ)} (∂_{((0, 1) : ℝ × ℝ)} T) := by
  sorry
