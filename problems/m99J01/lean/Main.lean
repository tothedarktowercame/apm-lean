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
  have hexists_fixed : ∃ ξ : ℝ, Real.cos ξ = ξ := by
    let g : ℝ → ℝ := fun x ↦ Real.cos x - x
    have hg : Continuous g := Real.continuous_cos.sub continuous_id
    have hz : (0 : ℝ) ∈ Set.Icc (g 1) (g 0) := by
      refine ⟨?_, ?_⟩
      · exact sub_nonpos.mpr (Real.cos_le_one 1)
      · simp [g]
    obtain ⟨ξ, _hξ, hξ⟩ :=
      intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hg.continuousOn hz
    exact ⟨ξ, sub_eq_zero.mp hξ⟩
  /-
  Boundary: existence of a real cosine fixed point is proved above by the
  intermediate value theorem. Completing the frozen theorem requires global
  Picard--Lindelöf existence for the vector field `cos u - u`, half-line
  uniqueness for arbitrary global `C¹` extensions, strict uniqueness of the
  equilibrium, and the monotone-trapping convergence argument. I searched
  Mathlib's ODE flow/Picard--Lindelöf, global Lipschitz continuation, Grönwall,
  strict monotonicity, and autonomous-flow APIs; I did not find an assembled
  route from those APIs to this raw `deriv`-based solution predicate in this
  pass.
  -/
  sorry
