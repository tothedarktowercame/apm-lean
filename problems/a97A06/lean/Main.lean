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

/-- The integrand sin²(x)/x² (with value 1 at 0) is integrable on ℝ. -/
theorem apm_a97A06_integrable :
    IntegrableOn (fun x : ℝ => (Real.sin x) ^ 2 / x ^ 2) (Set.Ioi 0) volume := by sorry

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
      atTop (nhds 0) := by sorry

/-- The semicircular arc integral of 1/z² vanishes as R → ∞. -/
theorem apm_a97A06_arc_inv_sq_vanishes :
    Tendsto (fun R : ℝ => ‖∫ θ in (0:ℝ)..π,
      (1 / (R * Complex.exp (I * θ)) ^ 2) * (I * R * Complex.exp (I * θ))‖)
      atTop (nhds 0) := by sorry

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
