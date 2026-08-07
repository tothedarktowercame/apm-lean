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

noncomputable def apm_m99j01_vectorField (x : ℝ) : ℝ := Real.cos x - x

/-- The autonomous vector field has the global Lipschitz bound needed by
Picard--Lindelöf and Grönwall uniqueness. -/
lemma apm_m99j01_vectorField_lipschitz :
    LipschitzWith 2 apm_m99j01_vectorField := by
  change LipschitzWith 2 (fun x : ℝ => Real.cos x - x)
  convert Real.lipschitzWith_cos.sub LipschitzWith.id using 1 <;> norm_num

/-- Every cosine fixed point gives the constant equilibrium solution in the
raw global-`C¹` encoding. -/
lemma apm_m99j01_fixed_isSolution {ξ : ℝ} (hξ : Real.cos ξ = ξ) :
    apm_m99j01_IsSolution ξ (fun _ => ξ) := by
  refine ⟨contDiff_const, rfl, ?_⟩
  intro t ht
  simpa [hξ]

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
  Boundary (closer hop 1): existence and uniqueness of the real cosine fixed point are proved
  above by the intermediate value theorem and `Real.strictAntiOn_cos`.
  This hop adds `apm_m99j01_vectorField_lipschitz`, proving the exact global
  Lipschitz constant `2` by combining `Real.lipschitzWith_cos` with
  `LipschitzWith.id`, and `apm_m99j01_fixed_isSolution`, which bundles every
  fixed point as the constant equilibrium in the frozen solution predicate.
  (Sibling: m00A05)

  Completing the frozen theorem requires global
  Picard--Lindelöf existence for the vector field `cos u - u`, half-line
  uniqueness for arbitrary global `C¹` extensions and the monotone-trapping
  convergence argument. I searched
  Mathlib's ODE flow/Picard--Lindelöf, global Lipschitz continuation, Grönwall,
  strict monotonicity, and autonomous-flow APIs; I did not find an assembled
  route from those APIs to this raw `deriv`-based solution predicate in this
  pass. Sibling `m00A05` reaches the same remaining globalization boundary;
  `m93J06`, `m96A02`, and `m96J02` likewise do not provide a closed global
  representative construction. Mathlib's `ODE_solution_unique_univ` can close
  uniqueness once a global `HasDerivAt` solution exists, but local Picard output
  is still interval-based and does not directly construct the required global
  `ContDiff ℝ 1` extension.
  -/
  sorry
