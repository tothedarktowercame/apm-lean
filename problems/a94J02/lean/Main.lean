import Mathlib

/-!
# APM a94J02 — an absolutely continuous strictly increasing function

## Statement repairs

The domain is changed from all of `ℝ` to `[0,1]`. The literal source is
inconsistent: a nonnegative strictly monotone function on `ℝ` cannot be
Lebesgue integrable, since one of its half-lines has a positive constant lower
bound. The compact-interval version is the standard intended problem.

Absolute continuity and integrability are stated explicitly, rather than only
suggested by the construction.
-/

open MeasureTheory Set

noncomputable section

theorem apm_a94j02 :
    ∃ h : ℝ → ℝ,
      AbsolutelyContinuousOnInterval h 0 1 ∧
      IntervalIntegrable h volume 0 1 ∧
      (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ h x) ∧
      StrictMonoOn h (Icc (0 : ℝ) 1) ∧
      0 < volume {x ∈ Icc (0 : ℝ) 1 | HasDerivAt h 0 x} := by
  sorry
