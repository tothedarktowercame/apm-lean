import Mathlib

open Complex Metric Set

noncomputable section

/-!
# APM a94A09

## Statement repairs

None.

## Encoding notes

A function whose source is the closed disk is represented by a function on `ℂ`,
with continuity required only on `closedBall 0 1` and analyticity only on
`ball 0 1`. The boundary `∂Δ` is `sphere 0 1`.
-/

theorem apm_a94a09
    {f : ℂ → ℂ}
    (hf_continuous : ContinuousOn f (closedBall 0 1))
    (hf_analytic : DifferentiableOn ℂ f (ball 0 1))
    (hf_boundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hf_no_boundary_fixed_point : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ z) :
    ∃! z : ℂ, z ∈ ball 0 1 ∧ f z = z := by
  sorry
