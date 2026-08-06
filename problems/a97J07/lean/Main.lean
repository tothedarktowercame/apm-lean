import Mathlib

/-!
# APM a97J07

## Statement repairs

None.

## Encoding questions

None. Analyticity on the open disk is encoded as complex differentiability
there, and the two boundary estimates retain the source's strict upper- and
lower-semicircle hypotheses.
-/

open Complex Metric Set

theorem apm_a97j07 (f : ℂ → ℂ) (a b : ℝ)
    (hf_cont : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hf_analytic : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (ha : ∀ z ∈ sphere (0 : ℂ) 1, 0 < z.im → ‖f z‖ ≤ a)
    (hb : ∀ z ∈ sphere (0 : ℂ) 1, z.im < 0 → ‖f z‖ ≤ b) :
    ‖f 0‖ ≤ Real.sqrt (a * b) := by
  sorry
