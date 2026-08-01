/-
! # APM a95J08: Young's convolution inequality — f ∈ L¹, g ∈ Lp implies f*g ∈ Lp

(a) For a.e. x, y ↦ f(x-y)g(y) is in L¹.
(b) ‖f*g‖_p ≤ ‖f‖₁ · ‖g‖_p (Young's inequality, case (1,p,p)).

The reusable convolution definition and Young inequality are promoted to
`ConstructionTargets.YoungConvolution`; this problem file retains its
problem-specific integrability result and a named re-export of part (b).
-/

import ConstructionTargets.YoungConvolution

open MeasureTheory Set Filter
open scoped ENNReal

open ConstructionTargets.YoungConvolution

noncomputable section

/-- Translation invariance: ∫|f(x-y)| dx = ∫|f(x)| dx for all y. -/
lemma integral_translate_norm
    {f : ℝ → ℝ} (hf : Integrable f volume) (y : ℝ) :
    ∫ x, ‖f (x - y)‖ ∂volume = ∫ x, ‖f x‖ ∂volume := by
  exact integral_sub_right_eq_self (μ := volume) (fun x : ℝ ↦ ‖f x‖) y

/-- (a) The integrand f(x-·)g(·) is in L¹ for a.e. x.

Split `g` into its bounded part on `{‖g‖ ≤ 1}` and its integrable part on
`{1 < ‖g‖}`. The first product is dominated pointwise by a translate of `‖f‖`;
the second follows from Fubini for the convolution of two integrable functions. -/
theorem convolution_integrand_integrableAE
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : MemLp g p volume) :
    ∀ᵐ x ∂volume,
      Integrable (fun y => f (x - y) * g y) volume := by
  let s : Set ℝ := {y | 1 < ‖g y‖}
  have hs : NullMeasurableSet s volume :=
    aestronglyMeasurable_const.nullMeasurableSet_lt hg.1.norm
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hp_real : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp' hp.le
  have hlarge_meas : AEStronglyMeasurable (s.indicator g) volume :=
    hg.1.indicator₀ hs
  have hlarge : Integrable (s.indicator g) volume := by
    refine (hg.integrable_norm_rpow hp0 hp').mono' hlarge_meas ?_
    filter_upwards with y
    by_cases hy : y ∈ s
    · simpa [hy] using Real.self_le_rpow_of_one_le (le_of_lt hy) hp_real
    · simp [hy]
      positivity
  have hsmall_meas : AEStronglyMeasurable (sᶜ.indicator g) volume :=
    hg.1.indicator₀ hs.compl
  have hsmall : ∀ x : ℝ, Integrable (fun y => f (x - y) * sᶜ.indicator g y) volume := by
    intro x
    refine (hf.comp_sub_left x).norm.mono'
      ((hf.comp_sub_left x).aestronglyMeasurable.mul hsmall_meas) ?_
    filter_upwards with y
    by_cases hy : y ∈ s
    · simp [hy]
    · have hyg : ‖g y‖ ≤ 1 := not_lt.mp hy
      have hind : sᶜ.indicator g y = g y := by simp [Set.indicator, hy]
      rw [norm_mul, hind]
      exact mul_le_of_le_one_right (norm_nonneg _) hyg
  have hlarge_ae :
      ∀ᵐ x ∂volume, Integrable (fun y => s.indicator g y * f (x - y)) volume :=
    hlarge.ae_convolution_exists (L := ContinuousLinearMap.mul ℝ ℝ) hf
  filter_upwards [hlarge_ae] with x hx
  have hx' : Integrable (fun y => f (x - y) * s.indicator g y) volume :=
    hx.congr (Eventually.of_forall fun y => mul_comm _ _)
  refine (hx'.add (hsmall x)).congr (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ s <;> simp [hy]

/-- (b) Named problem-level re-export of Young's convolution inequality. -/
theorem young_convolution_inequality
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : MemLp g p volume) :
    eLpNorm (convolution f g) p volume ≤
      eLpNorm f 1 volume * eLpNorm g p volume :=
  ConstructionTargets.YoungConvolution.young_convolution_inequality hp hp' hf hg

end
