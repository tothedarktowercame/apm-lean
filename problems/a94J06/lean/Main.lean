import Mathlib

/-!
# APM a94J06 — a conjugate contour integral on the unit circle

## Statement repairs

None.

The theorem states all three cases. For a point on the circle, the ordinary
contour integral is not defined because the parametrized integrand is not
integrable; no principal-value convention is silently introduced.
-/

open Complex Real MeasureTheory Metric Set Filter

noncomputable section

def apm_a94J06_integrand (z ζ : ℂ) : ℂ :=
  starRingEnd ℂ ζ / (ζ - z)

/-- On the unit circle, conjugation agrees with inversion. Reused from the
sorry-free inside/outside development at commit `6bbe1d7`. -/
lemma apm_a94J06_conj_eq_inv_on_circle {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    starRingEnd ℂ ζ = ζ⁻¹ :=
  (RCLike.inv_eq_conj hζ).symm

/-- Rational form of the conjugate integrand on the contour. -/
lemma apm_a94J06_integrand_eq_rational
    {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hne : ζ ≠ z) :
    apm_a94J06_integrand z ζ = (ζ * (ζ - z))⁻¹ := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h] at hζ
    simp at hζ
  rw [apm_a94J06_integrand, div_eq_inv_mul,
    apm_a94J06_conj_eq_inv_on_circle hζ, mul_inv_rev]

/-- The contour integral can be rationalized pointwise, including at the pole
where both expressions use Mathlib's totalized inverse. -/
lemma apm_a94J06_integral_eq_rational {z : ℂ} :
    (∮ ζ in C(0, 1), apm_a94J06_integrand z ζ) =
      ∮ ζ in C(0, 1), ((ζ * (ζ - z))⁻¹ : ℂ) := by
  apply circleIntegral.integral_congr zero_le_one
  intro ζ hζ
  have hζn : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  by_cases hne : ζ = z
  · subst hne
    simp [apm_a94J06_integrand, div_eq_inv_mul]
  · exact apm_a94J06_integrand_eq_rational hζn hne

namespace APM94A6

/-- On the unit circle |ζ| = 1, the conjugate satisfies ζ̄ = ζ⁻¹. -/
lemma conj_eq_inv_on_circle {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    starRingEnd ℂ ζ = ζ⁻¹ :=
  (RCLike.inv_eq_conj hζ).symm

/-- Pointwise: ζ̄/(ζ-z) = (ζ * (ζ-z))⁻¹ when |ζ| = 1 and ζ ≠ z. -/
lemma integrand_eq_rational {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hne : ζ ≠ z) :
    starRingEnd ℂ ζ / (ζ - z) = (ζ * (ζ - z))⁻¹ := by
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hζ; simp at hζ
  rw [div_eq_inv_mul, conj_eq_inv_on_circle hζ, mul_inv_rev]

/-- Partial fractions: (ζ(ζ-z))⁻¹ = z⁻¹ * ((ζ-z)⁻¹ - ζ⁻¹). -/
lemma partial_fractions {ζ z : ℂ} (hζ : ζ ≠ 0) (hz : z ≠ 0) (hζz : ζ ≠ z) :
    (ζ * (ζ - z))⁻¹ = z⁻¹ * ((ζ - z)⁻¹ - ζ⁻¹) := by
  have hζz2 : ζ - z ≠ 0 := sub_ne_zero.mpr hζz
  field_simp
  ring

/-- Replace conj integrand by rational form under the integral. -/
lemma integral_eq_rational {z : ℂ} :
    (∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z)) =
      ∮ ζ in C(0, 1), ((ζ * (ζ - z))⁻¹ : ℂ) := by
  apply circleIntegral.integral_congr zero_le_one
  intro ζ hζ
  have hζn : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  by_cases hne : ζ = z
  · subst hne; simp [div_eq_inv_mul]
  · exact integrand_eq_rational hζn hne

/-- Partial fractions under the integral. Since ‖z‖ ≠ 1, z is not on the unit
    circle, so ζ ≠ z for all ζ on the circle, and the identity holds
    everywhere on the circle. -/
lemma integral_partial_fractions {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ ≠ 1) :
    (∮ ζ in C(0, 1), ((ζ * (ζ - z))⁻¹ : ℂ)) =
      ∮ ζ in C(0, 1), (z⁻¹ * ((ζ - z)⁻¹ - ζ⁻¹) : ℂ) := by
  apply circleIntegral.integral_congr zero_le_one
  intro ζ hζ
  have hζn : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hζn; simp at hζn
  have hζz : ζ ≠ z := fun h => hz1 (h ▸ hζn)
  exact partial_fractions hζ0 hz0 hζz

/-- CircleIntegrable for `(z-w)⁻¹` when w is not on the unit circle. -/
lemma circleIntegrable_sub_inv_of_not_on_circle {w : ℂ} (hw : ‖w‖ ≠ 1) :
    CircleIntegrable (fun z => (z - w)⁻¹) 0 1 := by
  simp only [circleIntegrable_sub_inv_iff, abs_of_pos one_pos, one_ne_zero,
    mem_sphere_zero_iff_norm]
  exact Or.inr hw

/-- ∮ (ζ-w)⁻¹ = 2πi when ‖w‖ < 1. -/
lemma integral_sub_inv_of_mem {w : ℂ} (hw : ‖w‖ < 1) :
    (∮ ζ in C(0, 1), (ζ - w)⁻¹) = 2 * π * I :=
  circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_zero_iff.mpr hw)

/-- ∮ (ζ-w)⁻¹ = 0 when ‖w‖ > 1 (Cauchy-Goursat). -/
lemma integral_sub_inv_eq_zero {w : ℂ} (hw : 1 < ‖w‖) :
    (∮ ζ in C(0, 1), (ζ - w)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (R := 1) zero_le_one countable_empty
  · exact ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun ζ hζ => by
      refine sub_ne_zero.mpr ?_
      intro heq
      rw [heq] at hζ
      exact absurd (mem_closedBall_zero_iff.mp hζ) (not_le_of_gt hw)
  · rintro ζ hζ
    refine DifferentiableAt.inv (differentiableAt_id.sub_const _) ?_
    exact sub_ne_zero.mpr (fun heq => by
      have hball : ‖w‖ < 1 := heq ▸ mem_ball_zero_iff.mp hζ.1
      exact absurd hball (not_lt_of_gt hw))

/-- ∮ ζ⁻¹ = 2πi (center point). -/
lemma integral_sub_center_inv :
    (∮ ζ in C(0, 1), (ζ⁻¹ : ℂ)) = 2 * π * I := by
  convert circleIntegral.integral_sub_center_inv 0 one_ne_zero using 2
  funext ζ
  rw [sub_zero]

/-- z = 0 case: ∮ ζ̄/ζ dζ = 0 (integrand becomes ζ⁻², residue 0). -/
theorem apm_a94J06_at_zero :
    (∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - 0)) = 0 := by
  rw [integral_eq_rational]
  rw [circleIntegral.integral_congr zero_le_one (fun ζ _ => by
    show ((ζ : ℂ) * (ζ - 0))⁻¹ = ((ζ - 0) ^ (-2 : ℤ) : ℂ)
    rw [sub_zero, ← pow_two]
    rfl)]
  exact circleIntegral.integral_sub_zpow_of_ne (by decide : (-2 : ℤ) ≠ -1) 0 0 1

/-- Inside case, z ≠ 0: ∮ ζ̄/(ζ-z) dζ = 0. -/
theorem apm_a94J06_inside_nonzero {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    (∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z)) = 0 := by
  rw [integral_eq_rational, integral_partial_fractions hz0 (ne_of_lt hz)]
  rw [circleIntegral.integral_const_mul]
  have hne_z : ‖z‖ ≠ 1 := ne_of_lt hz
  have hne_0 : ‖(0 : ℂ)‖ ≠ 1 := by norm_num
  have hI1 : CircleIntegrable (fun ζ : ℂ => (ζ - z)⁻¹) 0 1 :=
    circleIntegrable_sub_inv_of_not_on_circle hne_z
  have hI2 : CircleIntegrable (fun ζ : ℂ => (ζ⁻¹ : ℂ)) 0 1 := by
    convert circleIntegrable_sub_inv_of_not_on_circle hne_0 using 1
    ext ζ; rw [sub_zero]
  rw [circleIntegral.integral_sub hI1 hI2]
  rw [integral_sub_inv_of_mem hz, integral_sub_center_inv]
  rw [show (2 * π * I : ℂ) - 2 * π * I = 0 from by ring]
  rw [mul_zero]

/-- Inside case (|z| < 1): ∮ ζ̄/(ζ-z) dζ = 0. -/
theorem apm_a94J06_inside {z : ℂ} (hz : ‖z‖ < 1) :
    (∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z)) = 0 := by
  by_cases hz0 : z = 0
  · subst hz0; exact apm_a94J06_at_zero
  · exact apm_a94J06_inside_nonzero hz hz0

/-- Outside case (|z| > 1): ∮ ζ̄/(ζ-z) dζ = -2πi/z. -/
theorem apm_a94J06_outside {z : ℂ} (hz : 1 < ‖z‖) :
    (∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z)) = -(2 * π * I) / z := by
  have hz0 : z ≠ 0 := by intro h; subst h; exact absurd hz (by simp)
  rw [integral_eq_rational, integral_partial_fractions hz0 (ne_of_gt hz)]
  rw [circleIntegral.integral_const_mul]
  have hne_z : ‖z‖ ≠ 1 := ne_of_gt hz
  have hne_0 : ‖(0 : ℂ)‖ ≠ 1 := by norm_num
  have hI1 : CircleIntegrable (fun ζ : ℂ => (ζ - z)⁻¹) 0 1 :=
    circleIntegrable_sub_inv_of_not_on_circle hne_z
  have hI2 : CircleIntegrable (fun ζ : ℂ => (ζ⁻¹ : ℂ)) 0 1 := by
    convert circleIntegrable_sub_inv_of_not_on_circle hne_0 using 1
    ext ζ; rw [sub_zero]
  rw [circleIntegral.integral_sub hI1 hI2]
  rw [integral_sub_inv_eq_zero hz, integral_sub_center_inv]
  rw [show (0 : ℂ) - 2 * π * I = -(2 * π * I) from by ring]
  -- Goal: z⁻¹ * -(2*π*I) = -(2*π*I) / z
  rw [div_eq_inv_mul, mul_comm]

end APM94A6


/-- Multiplication by the conjugate numerator does not change the norm on
the unit circle, so integrability would imply integrability of the bare
Cauchy kernel. -/
lemma apm_a94J06_not_circleIntegrable_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    ¬CircleIntegrable (apm_a94J06_integrand z) 0 1 := by
  intro hint
  have hkernel : CircleIntegrable (fun ζ : ℂ => (ζ - z)⁻¹) 0 1 := by
    have hnorm := hint.norm
    change IntervalIntegrable
      (fun θ : ℝ => ‖apm_a94J06_integrand z (circleMap 0 1 θ)‖)
      volume 0 (2 * π) at hnorm
    change IntervalIntegrable (fun θ : ℝ => (circleMap 0 1 θ - z)⁻¹)
      volume 0 (2 * π)
    have hmeas : AEStronglyMeasurable
        (fun θ : ℝ => (circleMap 0 1 θ - z)⁻¹)
        (volume.restrict (Set.uIoc 0 (2 * π))) :=
      (((measurable_circleMap 0 1).sub_const z).inv).aestronglyMeasurable
    apply (IntervalIntegrable.intervalIntegrable_norm_iff hmeas).mp
    convert hnorm using 1
    funext θ
    simp [apm_a94J06_integrand, norm_div, norm_circleMap_zero]
  rw [circleIntegrable_sub_inv_iff] at hkernel
  rcases hkernel with hzero | hout
  · norm_num at hzero
  · exact hout (by simpa [hz])


theorem apm_a94j06 (z : ℂ) :
    (‖z‖ < 1 →
      (∮ ζ in C(0, 1), apm_a94J06_integrand z ζ) = 0) ∧
    (1 < ‖z‖ →
      (∮ ζ in C(0, 1), apm_a94J06_integrand z ζ) =
        -(2 * Real.pi * Complex.I) / z) ∧
    (‖z‖ = 1 →
      ¬CircleIntegrable (apm_a94J06_integrand z) 0 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    exact APM94A6.apm_a94J06_inside hz
  · intro hz
    exact APM94A6.apm_a94J06_outside hz
  · exact apm_a94J06_not_circleIntegrable_of_norm_eq_one
