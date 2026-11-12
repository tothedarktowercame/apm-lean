import Mathlib
import ConstructionTargets.UpperSemicircleCauchy

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

/-- On every positive-radius upper semicircle, the arc integral of `F`
splits into its exponential, inverse-square, and inverse terms. -/
lemma apm_a97A06_arc_F_eq (R : ℝ) (hR : 0 < R) :
    (∫ θ in (0 : ℝ)..π,
      apm_a97A06_F (R * Complex.exp (I * θ)) *
        (I * R * Complex.exp (I * θ))) =
      (∫ θ in (0 : ℝ)..π,
        (Complex.exp (2 * I * (R * Complex.exp (I * θ))) /
          (R * Complex.exp (I * θ)) ^ 2) *
          (I * R * Complex.exp (I * θ))) -
      (∫ θ in (0 : ℝ)..π,
        (1 / (R * Complex.exp (I * θ)) ^ 2) *
          (I * R * Complex.exp (I * θ))) -
      π • (2 * I * I) := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hpoint (θ : ℝ) :
      apm_a97A06_F (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ)) =
        (Complex.exp (2 * I * (R * Complex.exp (I * θ))) /
            (R * Complex.exp (I * θ)) ^ 2) *
            (I * R * Complex.exp (I * θ)) -
        (1 / (R * Complex.exp (I * θ)) ^ 2) *
            (I * R * Complex.exp (I * θ)) -
        2 * I * ((1 / (R * Complex.exp (I * θ))) *
            (I * R * Complex.exp (I * θ))) := by
    have hz : (R : ℂ) * Complex.exp (I * θ) ≠ 0 :=
      mul_ne_zero hR0 (Complex.exp_ne_zero _)
    rw [apm_a97A06_F, if_neg hz]
    field_simp [hz]
  rw [intervalIntegral.integral_congr (fun θ _ => hpoint θ)]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub]
  · congr 1
    calc
      (∫ θ in (0 : ℝ)..π,
          2 * I * ((1 / (R * Complex.exp (I * θ))) *
            (I * R * Complex.exp (I * θ)))) =
          ∫ _θ in (0 : ℝ)..π, (2 * I * I : ℂ) := by
            apply intervalIntegral.integral_congr
            intro θ _
            have hz : (R : ℂ) * Complex.exp (I * θ) ≠ 0 :=
              mul_ne_zero hR0 (Complex.exp_ne_zero _)
            field_simp [hz]
      _ = π • (2 * I * I) := by
        rw [intervalIntegral.integral_const, sub_zero]
        rfl
  all_goals
    apply Continuous.intervalIntegrable <;>
    fun_prop (disch := aesop)

/-- The upper-semicircle arc integral of `F` tends to `2π`.  The first two
principal terms vanish, while `-2i/z` contributes `2π`. -/
theorem apm_a97A06_arc_F_tendsto :
    Tendsto (fun R : ℝ => ∫ θ in (0 : ℝ)..π,
      apm_a97A06_F (R * Complex.exp (I * θ)) *
        (I * R * Complex.exp (I * θ))) atTop (𝓝 (2 * π)) := by
  have hexp : Tendsto (fun R : ℝ => ∫ θ in (0 : ℝ)..π,
      (Complex.exp (2 * I * (R * Complex.exp (I * θ))) /
        (R * Complex.exp (I * θ)) ^ 2) *
        (I * R * Complex.exp (I * θ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact apm_a97A06_arc_exp_vanishes
  have hinv : Tendsto (fun R : ℝ => ∫ θ in (0 : ℝ)..π,
      (1 / (R * Complex.exp (I * θ)) ^ 2) *
        (I * R * Complex.exp (I * θ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact apm_a97A06_arc_inv_sq_vanishes
  have hconst : Tendsto (fun _ : ℝ => π • (2 * I * I : ℂ))
      atTop (𝓝 (π • (2 * I * I : ℂ))) := tendsto_const_nhds
  have hlim : Tendsto (fun R : ℝ =>
      (∫ θ in (0 : ℝ)..π,
        (Complex.exp (2 * I * (R * Complex.exp (I * θ))) /
          (R * Complex.exp (I * θ)) ^ 2) *
          (I * R * Complex.exp (I * θ))) -
      (∫ θ in (0 : ℝ)..π,
        (1 / (R * Complex.exp (I * θ)) ^ 2) *
          (I * R * Complex.exp (I * θ))) -
      π • (2 * I * I : ℂ)) atTop
      (𝓝 ((0 : ℂ) - 0 - π • (2 * I * I : ℂ))) :=
    (hexp.sub hinv).sub hconst
  have hvalue : ((0 : ℂ) - 0 - π • (2 * I * I : ℂ)) = 2 * π := by
    have hII : (2 * I * I : ℂ) = -2 := by
      rw [show (2 : ℂ) * I * I = 2 * (I * I) by ring, I_mul_I]
      norm_num
    rw [hII]
    norm_num
    ring
  rw [hvalue] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (apm_a97A06_arc_F_eq R hR).symm

/-- Cauchy's theorem on the upper semicircle forces the diameter integral of
`F` to tend to `-2π`. -/
theorem apm_a97A06_diameter_F_tendsto :
    Tendsto (fun R : ℝ => ∫ x in -R..R, apm_a97A06_F x)
      atTop (𝓝 (-2 * π)) := by
  have hdiff : Differentiable ℂ apm_a97A06_F :=
    differentiableOn_univ.mp apm_a97A06_F_analytic.differentiableOn
  have hcauchy (R : ℝ) :=
    ConstructionTargets.UpperSemicircleCauchy.intervalIntegral_add_upperSemicircle_eq_zero
      apm_a97A06_F hdiff R
  have hneg : Tendsto (fun R : ℝ =>
      -(∫ θ in (0 : ℝ)..π,
        apm_a97A06_F (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ)))) atTop (𝓝 (-2 * π)) := by
    convert apm_a97A06_arc_F_tendsto.neg using 1 <;> ring
  refine hneg.congr' ?_
  filter_upwards with R
  exact (eq_neg_of_add_eq_zero_left (hcauchy R)).symm

/-- The real part of the diameter contour integral is four times the negative
of the target finite integral. -/
lemma apm_a97A06_diameter_re_eq (R : ℝ) (_hR : 0 ≤ R) :
    (∫ x in -R..R, apm_a97A06_F x).re =
      -4 * ∫ x in (0 : ℝ)..R, Real.sin x ^ 2 / x ^ 2 := by
  have hdiff : Differentiable ℂ apm_a97A06_F :=
    differentiableOn_univ.mp apm_a97A06_F_analytic.differentiableOn
  have hFcont : Continuous (fun x : ℝ => apm_a97A06_F (x : ℂ)) :=
    hdiff.continuous.comp continuous_ofReal
  have hre :
      (∫ x in -R..R, apm_a97A06_F x).re =
        ∫ x in -R..R, (apm_a97A06_F x).re := by
    symm
    exact (RCLike.reCLM.intervalIntegral_comp_comm
      (hFcont.intervalIntegrable (μ := volume) (-R) R))
  rw [hre]
  have hreal : (∫ x in -R..R, (apm_a97A06_F x).re) =
      ∫ x in -R..R, -2 * (Real.sin x) ^ 2 / x ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    intro _
    exact apm_a97A06_real_part x hx
  rw [hreal]
  have heven (x : ℝ) :
      (-2 * Real.sin (-x) ^ 2 / (-x) ^ 2) =
        -2 * Real.sin x ^ 2 / x ^ 2 := by simp
  have hneg : (∫ x in -R..(0 : ℝ), -2 * Real.sin x ^ 2 / x ^ 2) =
      ∫ x in (0 : ℝ)..R, -2 * Real.sin x ^ 2 / x ^ 2 := by
    calc
      _ = ∫ x in (0 : ℝ)..R,
          (fun y : ℝ => -2 * Real.sin y ^ 2 / y ^ 2) (-x) := by
        simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
          (f := fun x : ℝ => -2 * Real.sin x ^ 2 / x ^ 2)
          (a := 0) (b := R)).symm
      _ = _ := intervalIntegral.integral_congr (fun x _ => by simpa using heven x)
  have hrecont : Continuous (fun x : ℝ => (apm_a97A06_F (x : ℂ)).re) :=
    Complex.continuous_re.comp hFcont
  have hint (a b : ℝ) : IntervalIntegrable
      (fun x : ℝ => -2 * Real.sin x ^ 2 / x ^ 2) volume a b := by
    apply (hrecont.intervalIntegrable a b).congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x hx
    exact apm_a97A06_real_part x hx
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (-R) 0) (hint 0 R)]
  rw [hneg, ← two_mul]
  have hscale : (∫ x in (0 : ℝ)..R, -2 * Real.sin x ^ 2 / x ^ 2) =
      -2 * ∫ x in (0 : ℝ)..R, Real.sin x ^ 2 / x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hscale]
  ring

/-- Main result: ∫₀^∞ sin²(x)/x² dx = π/2. -/
theorem apm_a97A06_main :
    ∫ x in Set.Ioi (0:ℝ), (Real.sin x) ^ 2 / x ^ 2 = π / 2 := by
  have himproper := intervalIntegral_tendsto_integral_Ioi 0
    apm_a97A06_integrable tendsto_id
  have htarget : Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R,
      Real.sin x ^ 2 / x ^ 2) atTop (𝓝 (π / 2)) := by
    have hre : Tendsto (fun R : ℝ =>
        (∫ x in -R..R, apm_a97A06_F x).re) atTop (𝓝 (-2 * π)) := by
      convert Complex.continuous_re.continuousAt.tendsto.comp
        apm_a97A06_diameter_F_tendsto using 1 <;> simp
    have hscaled := hre.const_mul (-1 / 4)
    convert hscaled.congr' ?_ using 1 <;> ring
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    rw [apm_a97A06_diameter_re_eq R hR]
    ring
  exact tendsto_nhds_unique himproper htarget

#print axioms apm_a97A06_main
