import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# APM a92J06: Trigonometric integral via contour integration

**Problem.** Evaluate ∫₀²π 1/(2 + cos θ) dθ via contour integration.
**Answer: 2π/√3.**
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Real
open scoped Topology

namespace ApmCanaries.A92J06

/-- √3 > 1. -/
lemma sqrt_three_gt_one : 1 < sqrt 3 := by
  have h : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_one] at h

/-- (sqrt 3 : ℂ) ^ 2 = 3. -/
lemma sq_sqrt_three_complex : (sqrt 3 : ℂ) ^ 2 = 3 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)

/-- z² + 4z + 1 = (z - z₁)(z - z₂) where z₁ = -2+√3, z₂ = -2-√3. -/
lemma quadratic_factor (z : ℂ) :
    z ^ 2 + 4 * z + 1 = (z - ((-2 : ℂ) + (sqrt 3 : ℂ))) *
                        (z - ((-2 : ℂ) - (sqrt 3 : ℂ))) := by
  have h3 : (sqrt 3 : ℂ) ^ 2 = 3 := sq_sqrt_three_complex
  linear_combination h3

/-- |z₁| < 1: z₁ = -2+√3 has |z₁| = 2-√3 < 1. -/
lemma z1_norm_lt_one : ‖((-2 : ℂ) + (sqrt 3 : ℂ))‖ < 1 := by
  rw [show ‖((-2 : ℂ) + (sqrt 3 : ℂ))‖ = ‖(↑(sqrt 3 - 2) : ℂ)‖ by
    congr 1; simp; ring]
  rw [Complex.norm_real]
  rw [show ‖(sqrt 3 - 2 : ℝ)‖ = 2 - sqrt 3 by
    rw [Real.norm_eq_abs, abs_of_nonpos]
    · linarith
    · nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num),
                 Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), sqrt_three_gt_one]]
  linarith [sqrt_three_gt_one]

/-- |z₂| > 1: z₂ = -2-√3 has |z₂| = 2+√3 > 1. -/
lemma z2_norm_gt_one : 1 < ‖((-2 : ℂ) - (sqrt 3 : ℂ))‖ := by
  rw [show ‖((-2 : ℂ) - (sqrt 3 : ℂ))‖ = ‖(↑(-(sqrt 3 + 2)) : ℂ)‖ by
    congr 1; simp; ring]
  rw [Complex.norm_real]
  rw [show ‖(-((sqrt 3 + 2) : ℝ))‖ = sqrt 3 + 2 by
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg]
    linarith [sqrt_three_gt_one]]
  linarith [sqrt_three_gt_one]

/-- The contour integral ∮_{|z|=1} 2/(i(z²+4z+1)) dz = 2π/√3.

    The proof uses partial fractions, the circle Cauchy integral formula for
    the root inside the disk, and Cauchy--Goursat for the exterior root. -/
lemma contour_integral_eval :
    (∮ z in C((0 : ℂ), 1), (2 : ℂ) / (I * (z ^ 2 + 4 * z + 1))) =
      Complex.ofReal (2 * π / sqrt 3) := by
  let a : ℂ := (-2 : ℂ) + (sqrt 3 : ℂ)
  let b : ℂ := (-2 : ℂ) - (sqrt 3 : ℂ)
  have ha_ball : a ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right, a] using z1_norm_lt_one
  have hb_norm : 1 < ‖b‖ := by
    simpa [b] using z2_norm_gt_one
  have hb_ne (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) : z ≠ b := by
    intro h
    subst z
    exact (not_lt_of_ge (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)) hb_norm
  have ha_ne_sphere (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) 1) : z ≠ a := by
    intro h
    subst z
    have : ‖a‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    exact (ne_of_lt (by simpa [a] using z1_norm_lt_one)) this
  have hb_ne_sphere (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) 1) : z ≠ b :=
    hb_ne z (Metric.sphere_subset_closedBall hz)
  have hin :
      (∮ z in C((0 : ℂ), 1), (z - a)⁻¹) = 2 * π * I :=
    circleIntegral.integral_sub_inv_of_mem_ball ha_ball
  have hout :
      (∮ z in C((0 : ℂ), 1), (z - b)⁻¹) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable
      (R := 1) (c := (0 : ℂ)) (s := ∅) (by norm_num) Set.countable_empty
    · exact (continuousOn_id.sub continuousOn_const).inv₀ fun z hz =>
        sub_ne_zero.2 (hb_ne z hz)
    · intro z hz
      exact ((differentiableAt_id.sub_const b).inv
        (sub_ne_zero.2 (hb_ne z (Metric.ball_subset_closedBall hz.1))))
  have hcia : CircleIntegrable (fun z : ℂ => (z - a)⁻¹) 0 1 := by
    rw [circleIntegrable_sub_inv_iff]
    exact Or.inr fun ha => ha_ne_sphere a (by simpa using ha) rfl
  have hcib : CircleIntegrable (fun z : ℂ => (z - b)⁻¹) 0 1 := by
    rw [circleIntegrable_sub_inv_iff]
    exact Or.inr fun hb => hb_ne_sphere b (by simpa using hb) rfl
  have hsqrt : (sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)))
  have hpf (z : ℂ) (hza : z ≠ a) (hzb : z ≠ b) :
      (2 : ℂ) / (I * (z ^ 2 + 4 * z + 1)) =
        (1 / (I * (sqrt 3 : ℂ))) * ((z - a)⁻¹ - (z - b)⁻¹) := by
    rw [quadratic_factor]
    change 2 / (I * ((z - a) * (z - b))) =
      1 / (I * (sqrt 3 : ℂ)) * ((z - a)⁻¹ - (z - b)⁻¹)
    field_simp [sub_ne_zero.2 hza, sub_ne_zero.2 hzb, hsqrt]
    simp [a, b]
    ring
  calc
    (∮ z in C((0 : ℂ), 1), (2 : ℂ) / (I * (z ^ 2 + 4 * z + 1))) =
        ∮ z in C((0 : ℂ), 1),
          (1 / (I * (sqrt 3 : ℂ))) * ((z - a)⁻¹ - (z - b)⁻¹) := by
      apply circleIntegral.integral_congr (by norm_num)
      intro z hz
      exact hpf z (ha_ne_sphere z hz) (hb_ne_sphere z hz)
    _ = (1 / (I * (sqrt 3 : ℂ))) *
        ((∮ z in C((0 : ℂ), 1), (z - a)⁻¹) -
          ∮ z in C((0 : ℂ), 1), (z - b)⁻¹) := by
      rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub hcia hcib]
    _ = Complex.ofReal (2 * π / sqrt 3) := by
      rw [hin, hout, sub_zero]
      field_simp [hsqrt]
      norm_cast
      field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]

/-- Main theorem: ∫₀²π 1/(2 + cos θ) dθ = 2π/√3.

    This is obtained by unfolding the unit-circle parametrization in the
    preceding contour integral. -/
theorem integral_inv_two_plus_cos :
    ∫ θ in (0 : ℝ)..2 * π, 1 / (2 + Real.cos θ) = 2 * π / sqrt 3 := by
  have hden (θ : ℝ) : 2 + Real.cos θ ≠ 0 := by
    have := neg_one_le_cos θ
    linarith
  have hpoint (θ : ℝ) :
      deriv (circleMap (0 : ℂ) 1) θ *
          ((2 : ℂ) / (I * ((circleMap 0 1 θ) ^ 2 + 4 * circleMap 0 1 θ + 1))) =
        ((1 / (2 + Real.cos θ) : ℝ) : ℂ) := by
    let z : ℂ := circleMap 0 1 θ
    have hz : z ≠ 0 := by
      simp [z, circleMap_zero]
    have hsum : z + z⁻¹ = (2 * Real.cos θ : ℝ) := by
      have hw :
          ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) ≠ 0 := by
        simpa [z, circleMap_zero, Complex.exp_mul_I, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin] using hz
      have hwinv :
          ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)⁻¹ =
            (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
        field_simp [hw]
        rw [show
          ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) *
              ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) =
            ((Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 : ℝ) by
              push_cast
              ring_nf
              simp]
        rw [Real.sin_sq_add_cos_sq]
        norm_num
      simp only [z, circleMap_zero, ofReal_one, one_mul, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, hwinv]
      push_cast
      ring
    have hpoly :
        z ^ 2 + 4 * z + 1 = z * (2 * (2 + Real.cos θ : ℝ)) := by
      calc
        z ^ 2 + 4 * z + 1 = z * (z + 4 + z⁻¹) := by
          field_simp [hz]
        _ = z * (2 * (2 + Real.cos θ : ℝ)) := by
          rw [show z + 4 + z⁻¹ = (z + z⁻¹) + 4 by ring, hsum]
          push_cast
          ring
    rw [deriv_circleMap]
    change z * I * (2 / (I * (z ^ 2 + 4 * z + 1))) =
      ((1 / (2 + Real.cos θ) : ℝ) : ℂ)
    rw [hpoly]
    simp only [one_div, Complex.ofReal_inv]
    field_simp [hz, hden]
  rw [← Complex.ofReal_inj, ← intervalIntegral.integral_ofReal]
  rw [← contour_integral_eval, circleIntegral]
  apply intervalIntegral.integral_congr
  intro θ _
  simpa only [smul_eq_mul] using (hpoint θ).symm

end ApmCanaries.A92J06
