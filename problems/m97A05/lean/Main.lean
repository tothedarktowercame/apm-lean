import Mathlib.Analysis.Distribution.TemperedDistribution

/-! # APM m97A05: the distribution carried by the line `y = -x`

## Statement repairs

The displayed domain is repaired from `ℝ` to `ℝ²`, since the test function is
evaluated at `(s,-s)`.  Complex-valued Schwartz functions and Mathlib's Fourier
normalization are used, making this a tempered-distribution formulation.

Part (b) of the source (a formula for the Fourier transform of `T`) is NOT
encoded: the theorem below covers (a) via membership in `𝓢'`, folds (c) into
the identity `∂ₓT = ∂ᵧT`, and states (d) as the equality of the repeated
derivatives.  A faithful (b) needs the Fourier transform on `𝓢'(ℝ × ℝ, ℂ)`
applied to this specific `T`; record its addition here if encoded later.

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
