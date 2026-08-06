import Mathlib

/-!
# APM m99J01

## Statement repairs

None.

## Encoding questions

A solution on the half-line is represented by a `C¹` function on `ℝ`, with the
differential equation and uniqueness asserted only for nonnegative times. This avoids
mistakenly identifying arbitrary extensions to negative time as different solutions.
-/

def apm_m99j01_IsSolution (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 u ∧ u 0 = u₀ ∧
    ∀ t : ℝ, 0 ≤ t → deriv u t + u t = Real.cos (u t)

theorem apm_m99j01 :
    (∀ u₀ : ℝ,
      ∃ u : ℝ → ℝ,
        apm_m99j01_IsSolution u₀ u ∧
          ∀ v : ℝ → ℝ, apm_m99j01_IsSolution u₀ v →
            ∀ t : ℝ, 0 ≤ t → v t = u t) ∧
    ∃! ξ : ℝ,
      Real.cos ξ = ξ ∧
        ∀ (u₀ : ℝ) (u : ℝ → ℝ),
          apm_m99j01_IsSolution u₀ u →
            Filter.Tendsto u Filter.atTop (nhds ξ) := by
  sorry
