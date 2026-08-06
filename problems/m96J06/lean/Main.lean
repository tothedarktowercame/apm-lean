import Mathlib

/-!
# APM m96J06: A nonlinear functional equation near zero

## Statement repairs

None.

## Encoding questions

None. The open neighborhood is the explicit sup-norm ball
`{y ∈ C([-2,2]) | ‖y‖∞ < 1/48}`. Functions are represented on `ℝ` with all
continuity, bounds, and equations restricted to the exact interval `[-2,2]`.
-/

open Set

noncomputable section

def apm_m96J06_inNeighborhood (y : ℝ → ℝ) : Prop :=
  ContinuousOn y (Icc (-2 : ℝ) 2) ∧
  ∀ t ∈ Icc (-2 : ℝ) 2, |y t| < (1 / 48 : ℝ)

def apm_m96J06_isSolution (x y : ℝ → ℝ) : Prop :=
  ContinuousOn x (Icc (-2 : ℝ) 2) ∧
  ∀ t ∈ Icc (-2 : ℝ) 2,
    x t - 2 * x 0 + x (t / 2 + 1) * x (t / 2 - 1) = y t

theorem apm_m96j06 :
    ∀ y : ℝ → ℝ,
      apm_m96J06_inNeighborhood y →
        ∃ x : ℝ → ℝ,
          apm_m96J06_isSolution x y ∧
          ∀ t ∈ Icc (-2 : ℝ) 2, |x t| ≤ (1 / 12 : ℝ) := by
  sorry
