import Mathlib

open Complex Real MeasureTheory Filter Topology Set

noncomputable section

/-- The auxiliary entire function F(z) = (e^{2iz} - 1 - 2iz)/z²,
    extended to the entire function with F(0) = -2. -/
def apm_a97A06_F (z : ℂ) : ℂ :=
  if z = 0 then -2
  else (Complex.exp (2 * I * z) - 1 - 2 * I * z) / z ^ 2

/-- F is entire (analytic on all of ℂ). -/
theorem apm_a97A06_F_analytic : AnalyticOn ℂ apm_a97A06_F univ := by sorry

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

/-- Main result: ∫₀^∞ sin²(x)/x² dx = π/2. -/
theorem apm_a97A06_main :
    ∫ x in Set.Ioi (0:ℝ), (Real.sin x) ^ 2 / x ^ 2 = π / 2 := by sorry
