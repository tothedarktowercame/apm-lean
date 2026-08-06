import Mathlib

/-!
# APM m00A05: A globally attracting scalar ODE equilibrium

## Statement repairs

None.

## Encoding questions

None. Solutions are global real-function representatives whose required
regularity and equation are restricted to `[0,∞)`. Uniqueness is consequently
stated with `Set.EqOn` on that interval, so irrelevant negative-time values are
not accidentally constrained.
-/

open Set Filter
open scoped Topology

noncomputable section

def apm_m00A05_isSolution (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  ContinuousOn u (Ici 0) ∧
  DifferentiableOn ℝ u (Ioi 0) ∧
  u 0 = u₀ ∧
  ∀ t : ℝ, 0 < t → deriv u t + u t = Real.cos (u t)

theorem apm_m00a05 :
    (∀ u₀ : ℝ,
      ∃ u : ℝ → ℝ,
        apm_m00A05_isSolution u₀ u ∧
        ∀ v : ℝ → ℝ,
          apm_m00A05_isSolution u₀ v → EqOn u v (Ici 0)) ∧
    ∃ ξ : ℝ, Real.cos ξ = ξ ∧
      ∀ (u₀ : ℝ) (u : ℝ → ℝ),
        apm_m00A05_isSolution u₀ u →
        Tendsto u atTop (nhds ξ) := by
  sorry
