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

lemma apm_m99j01_cos_fixed_unique {x y : ℝ}
    (hx : Real.cos x = x) (hy : Real.cos y = y) : x = y := by
  have fixed_mem (z : ℝ) (hz : Real.cos z = z) : z ∈ Set.Icc (0 : ℝ) Real.pi := by
    have hz_lower : -(1 : ℝ) ≤ z := by rw [← hz]; exact Real.neg_one_le_cos z
    have hz_upper : z ≤ 1 := by rw [← hz]; exact Real.cos_le_one z
    have hz_pos : 0 < z := by
      rw [← hz]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_gt_three]
    exact ⟨hz_pos.le, by nlinarith [Real.pi_gt_three]⟩
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have := Real.strictAntiOn_cos (fixed_mem x hx) (fixed_mem y hy) hxy
    rw [hx, hy] at this
    exact (not_lt_of_ge hxy.le this).elim
  · exact hxy
  · have := Real.strictAntiOn_cos (fixed_mem y hy) (fixed_mem x hx) hxy
    rw [hx, hy] at this
    exact (not_lt_of_ge hxy.le this).elim

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
  have hexists_unique_fixed : ∃! ξ : ℝ, Real.cos ξ = ξ := by
    obtain ⟨ξ, hξ⟩ := hexists_fixed
    exact ⟨ξ, hξ, fun y hy => apm_m99j01_cos_fixed_unique hy hξ⟩
  /-
  Boundary: existence and uniqueness of the real cosine fixed point are proved
  above by the intermediate value theorem and `Real.strictAntiOn_cos`.
  Completing the frozen theorem requires global
  Picard--Lindelöf existence for the vector field `cos u - u`, half-line
  uniqueness for arbitrary global `C¹` extensions and the monotone-trapping
  convergence argument. I searched
  Mathlib's ODE flow/Picard--Lindelöf, global Lipschitz continuation, Grönwall,
  strict monotonicity, and autonomous-flow APIs; I did not find an assembled
  route from those APIs to this raw `deriv`-based solution predicate in this
  pass.
  -/
  sorry
