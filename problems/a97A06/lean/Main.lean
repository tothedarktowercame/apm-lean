import Mathlib
import ConstructionTargets.Sinc

open Complex Real MeasureTheory Filter Topology Set

noncomputable section

/-- The auxiliary entire function F(z) = (e^{2iz} - 1 - 2iz)/z²,
    extended to the entire function with F(0) = -2. -/
def apm_a97A06_F (z : ℂ) : ℂ :=
  if z = 0 then -2
  else (Complex.exp (2 * I * z) - 1 - 2 * I * z) / z ^ 2

private lemma apm_a97A06_F_continuousAt_zero :
    ContinuousAt apm_a97A06_F 0 := by
  let a : ℂ := 2 * I
  let r : ℂ → ℂ := fun w =>
    Complex.exp w - ∑ i ∈ Finset.range 3, w ^ i / (i.factorial : ℂ)
  have hlo : r =o[𝓝 0] (fun w : ℂ => w ^ 2) := by
    simpa [r] using Complex.exp_sub_sum_range_succ_isLittleO_pow 2
  have ha : Tendsto (fun z : ℂ => a * z) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_id :
      Tendsto (fun z : ℂ => a * z) (𝓝 0) (𝓝 (a * 0)))
  have hrem : Tendsto
      (fun z : ℂ => a ^ 2 * (r (a * z) / (a * z) ^ 2))
      (𝓝 0) (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul (hlo.tendsto_div_nhds_zero.comp ha))
  have hform : Tendsto (fun z : ℂ => a ^ 2 / 2 +
      a ^ 2 * (r (a * z) / (a * z) ^ 2)) (𝓝 0) (𝓝 (-2)) := by
    have ha2 : a ^ 2 / 2 = (-2 : ℂ) := by
      dsimp [a]
      rw [pow_two]
      calc
        2 * I * (2 * I) / 2 = 2 * (I * I) := by ring
        _ = -2 := by rw [I_mul_I]; norm_num
    simpa [ha2] using tendsto_const_nhds.add hrem
  have hF0 : apm_a97A06_F 0 = -2 := by simp [apm_a97A06_F]
  rw [continuousAt_iff_punctured_nhds, hF0]
  apply (hform.mono_left inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change z ≠ 0 at hz
  rw [apm_a97A06_F, if_neg hz]
  dsimp [r, a]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
    Nat.factorial_one, Nat.factorial_two]
  field_simp [hz, I_ne_zero]
  ring

/-- F is entire (analytic on all of ℂ). -/
theorem apm_a97A06_F_analytic : AnalyticOn ℂ apm_a97A06_F univ := by
  rw [Complex.analyticOn_iff_differentiableOn isOpen_univ]
  have hdiff : ∀ w : ℂ, w ≠ 0 → DifferentiableAt ℂ apm_a97A06_F w := by
    intro w hw
    have hquot : DifferentiableAt ℂ
        (fun z => (Complex.exp (2 * I * z) - 1 - 2 * I * z) / z ^ 2) w := by
      fun_prop (disch := aesop)
    apply hquot.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hw] with z hz
    simp [apm_a97A06_F, hz]
  intro z hzmem
  by_cases hz : z = 0
  · subst z
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (by
        filter_upwards [self_mem_nhdsWithin] with w hw
        change w ≠ 0 at hw
        exact hdiff w hw)
      apm_a97A06_F_continuousAt_zero).differentiableAt.differentiableWithinAt
  · exact (hdiff z hz).differentiableWithinAt

/-- The integrand sin²(x)/x² is integrable on the positive half-line. -/
theorem apm_a97A06_integrable :
    IntegrableOn (fun x : ℝ => (Real.sin x) ^ 2 / x ^ 2) (Set.Ioi 0) volume := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · refine (integrableOn_const (C := (1 : ℝ)) (μ := volume)
      (ne_of_lt ((measure_mono Ioc_subset_Icc_self).trans_lt (by simp)))).mono'
      ((Real.measurable_sin.pow_const 2).div (measurable_id.pow_const 2)).aestronglyMeasurable
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact (div_le_one (sq_pos_of_pos hx.1)).mpr (Real.sin_sq_le_sq (x := x))
  · have hp : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    refine hp.mono'
      ((Real.measurable_sin.pow_const 2).div (measurable_id.pow_const 2)).aestronglyMeasurable
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    calc
      Real.sin x ^ 2 / x ^ 2 ≤ 1 / x ^ 2 := by
        gcongr
        exact Real.sin_sq_le_one x
      _ = x ^ (-2 : ℝ) := by
        rw [Real.rpow_neg (le_of_lt (zero_lt_one.trans hx)), Real.rpow_two]
        ring

private def apm_a97A06_q (x : ℝ) := x * Real.sinc x ^ 2

private def apm_a97A06_d (x : ℝ) :=
  2 * Real.sinc (2 * x) - Real.sinc x ^ 2

private lemma apm_a97A06_q_hasDerivAt (x : ℝ) :
    HasDerivAt apm_a97A06_q (apm_a97A06_d x) x := by
  by_cases hx : x = 0
  · subst x
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h : Tendsto (fun y : ℝ => Real.sinc y ^ 2) (𝓝[≠] 0) (𝓝 1) := by
      have hc : Tendsto (fun y : ℝ => Real.sinc y ^ 2) (𝓝 0)
          (𝓝 (Real.sinc 0 ^ 2)) := (Real.continuous_sinc.pow 2).continuousAt
      simpa using hc.mono_left inf_le_left
    have hz : Tendsto
        (fun y : ℝ => y⁻¹ • (apm_a97A06_q (0 + y) - apm_a97A06_q 0))
        (𝓝[≠] 0) (𝓝 1) := by
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hq0 : apm_a97A06_q (0 + y) - apm_a97A06_q 0 =
          y * Real.sinc y ^ 2 := by simp [apm_a97A06_q]
      rw [hq0]
      change Real.sinc y ^ 2 = y⁻¹ * (y * Real.sinc y ^ 2)
      rw [← mul_assoc, inv_mul_cancel₀ hy, one_mul]
    convert hz using 1 <;> norm_num [apm_a97A06_d]
  · have hs0 : HasDerivAt (fun y : ℝ => Real.sin y / y)
        ((Real.cos x * x - Real.sin x) / x ^ 2) x := by
      simpa only [id_eq, mul_one] using
        (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
    have hs : HasDerivAt Real.sinc
        ((Real.cos x * x - Real.sin x) / x ^ 2) x := by
      apply hs0.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hx] with y hy
      exact Real.sinc_of_ne_zero hy
    have hq : HasDerivAt apm_a97A06_q
        (Real.sinc x ^ 2 + x * (2 * Real.sinc x *
          ((Real.cos x * x - Real.sin x) / x ^ 2))) x := by
      simpa [apm_a97A06_q, mul_assoc] using (hasDerivAt_id x).mul (hs.pow 2)
    convert hq using 1
    simp only [apm_a97A06_d, Real.sinc_of_ne_zero hx,
      Real.sinc_of_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hx)]
    rw [Real.sin_two_mul]
    field_simp
    ring

private lemma apm_a97A06_q_deriv (x : ℝ) :
    deriv apm_a97A06_q x = apm_a97A06_d x :=
  (apm_a97A06_q_hasDerivAt x).deriv

private lemma apm_a97A06_finite_identity (R : ℝ) :
    (∫ x in (0 : ℝ)..R, Real.sinc x ^ 2) =
      (∫ x in (0 : ℝ)..(2 * R), Real.sinc x) - R * Real.sinc R ^ 2 := by
  have hdcont : Continuous apm_a97A06_d :=
    ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).const_mul 2).sub
      (Real.continuous_sinc.pow 2)
  have hftc : (∫ x in (0 : ℝ)..R, apm_a97A06_d x) =
      apm_a97A06_q R - apm_a97A06_q 0 := by
    apply intervalIntegral.integral_deriv_eq_sub' apm_a97A06_q
    · funext x
      exact apm_a97A06_q_deriv x
    · intro x hx
      exact (apm_a97A06_q_hasDerivAt x).differentiableAt
    · exact hdcont.continuousOn
  have hscale : 2 * (∫ x in (0 : ℝ)..R, Real.sinc (2 * x)) =
      ∫ x in (0 : ℝ)..(2 * R), Real.sinc x := by
    have heq : (fun x : ℝ => Real.sinc (2 * x)) =
        fun x => Real.sinc (x * 2) := by
      funext x
      rw [mul_comm]
    calc
      2 * (∫ x in (0 : ℝ)..R, Real.sinc (2 * x)) =
          2 * (∫ x in (0 : ℝ)..R, Real.sinc (x * 2)) := by rw [heq]
      _ = ∫ x in (0 : ℝ)..(R * 2), Real.sinc x := by
        rw [intervalIntegral.integral_comp_mul_right Real.sinc
          (by norm_num : (2 : ℝ) ≠ 0)]
        simp
      _ = ∫ x in (0 : ℝ)..(2 * R), Real.sinc x := by ring_nf
  change (∫ x in (0 : ℝ)..R,
      2 * Real.sinc (2 * x) - Real.sinc x ^ 2) = _ at hftc
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul] at hftc
  · rw [hscale] at hftc
    simp [apm_a97A06_q] at hftc ⊢
    linarith
  · exact (Real.continuous_sinc.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 R |>.const_mul 2
  · exact (Real.continuous_sinc.pow 2).intervalIntegrable 0 R

private lemma apm_a97A06_tendsto_q_atTop :
    Tendsto apm_a97A06_q atTop (𝓝 0) := by
  refine squeeze_zero' (g := fun R : ℝ => 1 / R) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact mul_nonneg hR.le (sq_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [apm_a97A06_q, Real.sinc_of_ne_zero hR.ne']
    calc
      R * (Real.sin R / R) ^ 2 = Real.sin R ^ 2 / R := by field_simp
      _ ≤ 1 / R := div_le_div_of_nonneg_right (Real.sin_sq_le_one R) hR.le
  · simpa [one_div] using tendsto_inv_atTop_zero

private lemma apm_a97A06_tendsto_finite_identity :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x ^ 2)
      atTop (𝓝 (π / 2)) := by
  have hsinc := ConstructionTargets.Sinc.tendsto_integral_sinc_pi_div_two
  have htwo : Tendsto (fun R : ℝ => 2 * R) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hscaled := hsinc.comp htwo
  have hsub := hscaled.sub apm_a97A06_tendsto_q_atTop
  have hsub' : Tendsto
      (fun R : ℝ => (∫ x in (0 : ℝ)..(2 * R), Real.sinc x) -
        apm_a97A06_q R) atTop (𝓝 (π / 2)) := by
    simpa using hsub
  apply hsub'.congr'
  filter_upwards with R
  exact (apm_a97A06_finite_identity R).symm

/-- Real part identity: Re(F(x)) = -2 sin²(x)/x² for x ≠ 0. -/
theorem apm_a97A06_real_part
    (x : ℝ) (hx : x ≠ 0) :
    (apm_a97A06_F (x : ℂ)).re = -2 * (Real.sin x) ^ 2 / x ^ 2 := by
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast hx
  rw [apm_a97A06_F, if_neg hxC]
  rw [Complex.div_re]
  simp [Complex.normSq, pow_two, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg]
  field_simp [hx]
  have hmul : I * (x : ℂ) * 2 = ((2 * x : ℝ) : ℂ) * I := by
    simp [mul_assoc, mul_comm]
  rw [hmul, Complex.exp_mul_I]
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have hcos : (Complex.cos (2 * (x : ℂ))).re = Real.cos (2 * x) := by
    simpa using (Complex.cos_ofReal_re (2 * x))
  have hsin : (Complex.sin (2 * (x : ℂ))).im = 0 := by
    simpa using (Complex.sin_ofReal_im (2 * x))
  rw [hcos, hsin, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- The semicircular arc integral of e^{2iz}/z² vanishes as R → ∞. -/
theorem apm_a97A06_arc_exp_vanishes :
    Tendsto (fun R : ℝ => ‖∫ θ in (0:ℝ)..π,
      (Complex.exp (2 * I * (R * Complex.exp (I * θ))) /
       (R * Complex.exp (I * θ)) ^ 2) * (I * R * Complex.exp (I * θ))‖)
      atTop (nhds 0) := by
  refine squeeze_zero' (g := fun R : ℝ => π / R)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 1 / R) fun θ hθ => ?_).trans_eq ?_
    · have hθ' : θ ∈ Icc (0 : ℝ) π := by
        rw [uIoc_of_le Real.pi_pos.le] at hθ
        exact ⟨hθ.1.le, hθ.2⟩
      have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ'
      have hexp :
          ‖Complex.exp (2 * I * (R * Complex.exp (I * θ)))‖ ≤ 1 := by
        rw [Complex.norm_exp, Real.exp_le_one_iff]
        simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]
        positivity
      calc
        ‖(Complex.exp (2 * I * (R * Complex.exp (I * θ))) /
            (R * Complex.exp (I * θ)) ^ 2) *
            (I * R * Complex.exp (I * θ))‖ =
            ‖Complex.exp (2 * I * (R * Complex.exp (I * θ)))‖ / R := by
              simp [norm_pow, Complex.norm_exp_I_mul_ofReal, abs_of_pos hR]
              field_simp
        _ ≤ 1 / R := div_le_div_of_nonneg_right hexp hR.le
    · rw [sub_zero, abs_of_pos Real.pi_pos]
      ring
  · simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_inv_atTop_zero.mul_const π :
        Tendsto (fun R : ℝ => R⁻¹ * π) atTop (𝓝 (0 * π)))

/-- The semicircular arc integral of 1/z² vanishes as R → ∞. -/
theorem apm_a97A06_arc_inv_sq_vanishes :
    Tendsto (fun R : ℝ => ‖∫ θ in (0:ℝ)..π,
      (1 / (R * Complex.exp (I * θ)) ^ 2) * (I * R * Complex.exp (I * θ))‖)
      atTop (nhds 0) := by
  refine squeeze_zero' (g := fun R : ℝ => π / R)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 1 / R) fun θ hθ => ?_).trans_eq ?_
    · simp [norm_pow, Complex.norm_exp_I_mul_ofReal, abs_of_pos hR]
      field_simp
      norm_num
    · rw [sub_zero, abs_of_pos Real.pi_pos]
      ring
  · simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_inv_atTop_zero.mul_const π :
        Tendsto (fun R : ℝ => R⁻¹ * π) atTop (𝓝 (0 * π)))

/-- The arc integral of 1/z over the upper semicircle equals iπ. -/
theorem apm_a97A06_arc_inv_eq_iPi
    (R : ℝ) (hR : 0 < R) :
    ∫ θ in (0:ℝ)..π,
      (1 / (R * Complex.exp (I * θ))) * (I * R * Complex.exp (I * θ)) = I * π := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
  calc
    ∫ θ in (0 : ℝ)..π,
      (1 / (R * Complex.exp (I * θ))) * (I * R * Complex.exp (I * θ)) = ∫ θ in (0 : ℝ)..π, I := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with θ hθ
        field_simp [Complex.exp_ne_zero, hR0]
    _ = I * π := by
      rw [intervalIntegral.integral_const]
      rw [sub_zero]
      change ((π : ℂ) * I) = I * π
      simp [mul_comm]

/-- Main result: ∫₀^∞ sin²(x)/x² dx = π/2. -/
theorem apm_a97A06_main :
    ∫ x in Set.Ioi (0:ℝ), (Real.sin x) ^ 2 / x ^ 2 = π / 2 := by
  have himproper := intervalIntegral_tendsto_integral_Ioi 0
    apm_a97A06_integrable tendsto_id
  have heq : ∀ R : ℝ,
      (∫ x in (0 : ℝ)..R, Real.sin x ^ 2 / x ^ 2) =
        ∫ x in (0 : ℝ)..R, Real.sinc x ^ 2 := by
    intro R
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx0
    intro hx
    rw [Real.sinc_of_ne_zero hx0]
    field_simp
  have htarget : Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R,
      Real.sin x ^ 2 / x ^ 2) atTop (𝓝 (π / 2)) := by
    apply apm_a97A06_tendsto_finite_identity.congr'
    filter_upwards with R
    exact (heq R).symm
  exact tendsto_nhds_unique himproper htarget
