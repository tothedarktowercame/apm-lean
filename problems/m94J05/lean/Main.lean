import Mathlib

/-! # APM m94J05: a small nonlinear Euler boundary-value problem

## Statement repairs

None.
-/

open Set

def IsM94J05Solution (f x : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 x (Icc 1 2) ∧
  x 1 = 0 ∧ x 2 = 0 ∧
  ∀ t ∈ Icc (1 : ℝ) 2,
    t ^ 2 * iteratedDeriv 2 x t + 2 * t * deriv x t = f t + (x t) ^ 2

theorem apm_m94j05 :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : ℝ → ℝ,
      ContinuousOn f (Icc 1 2) →
      (∀ t ∈ Icc (1 : ℝ) 2, |f t| < ε) →
      ∃! x : ℝ → ℝ, IsM94J05Solution f x := by
  sorry
