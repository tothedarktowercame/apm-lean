import Mathlib
import ConstructionTargets.Sinc

/-!
# APM a96A08 — an improper sine integral

## Statement repairs

None.

The improper integral is encoded as the Lebesgue integral on `ℝ`. The values
at the removable singularities `0` and `1` do not affect the integral. The
statement includes integrability so the displayed value is meaningful.
-/

open MeasureTheory Real

noncomputable section

set_option maxHeartbeats 800000

def apm_a96A08_integrand (x : ℝ) : ℝ :=
  Real.sin (Real.pi * x) / (x ^ 2 - x)

private def apm_a96A08_extension (x : ℝ) : ℝ :=
  -(Real.pi * (Real.sinc (Real.pi * x) + Real.sinc (Real.pi * (x - 1))))

private lemma integrand_eq_extension {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    apm_a96A08_integrand x = apm_a96A08_extension x := by
  rw [apm_a96A08_integrand, apm_a96A08_extension,
    Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero h0),
    Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr h1))]
  rw [mul_sub, mul_one, Real.sin_sub]
  simp
  field_simp [h0, sub_ne_zero.mpr h1]
  all_goals ring

private lemma integrand_ae_eq_extension :
    apm_a96A08_integrand =ᵐ[volume] apm_a96A08_extension := by
  filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (1 : ℝ)] with x hx0 hx1
  exact integrand_eq_extension hx0 hx1

private lemma continuous_extension : Continuous apm_a96A08_extension := by
  unfold apm_a96A08_extension
  fun_prop

private lemma extension_bound_right {x : ℝ} (hx : 2 ≤ x) :
    ‖apm_a96A08_extension x‖ ≤ 3 * ‖(1 + x ^ 2)⁻¹‖ := by
  rw [← integrand_eq_extension (by linarith) (by linarith)]
  rw [apm_a96A08_integrand, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by nlinarith : 0 ≤ x ^ 2 - x)]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ 1 + x ^ 2))]
  have hs := abs_sin_le_one (Real.pi * x)
  apply (div_le_div_of_nonneg_right hs (by nlinarith : 0 ≤ x ^ 2 - x)).trans
  rw [div_le_iff₀ (by nlinarith : 0 < x ^ 2 - x)]
  rw [show 3 * (1 + x ^ 2)⁻¹ * (x ^ 2 - x) =
      (3 * (x ^ 2 - x)) / (1 + x ^ 2) by field_simp]
  rw [le_div_iff₀ (by nlinarith [sq_nonneg x] : 0 < 1 + x ^ 2)]
  nlinarith [sq_nonneg (x - 2)]

private lemma extension_bound_left {x : ℝ} (hx : x ≤ -2) :
    ‖apm_a96A08_extension x‖ ≤ 3 * ‖(1 + x ^ 2)⁻¹‖ := by
  rw [← integrand_eq_extension (by linarith) (by linarith)]
  rw [apm_a96A08_integrand, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by nlinarith : 0 ≤ x ^ 2 - x)]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ 1 + x ^ 2))]
  have hs := abs_sin_le_one (Real.pi * x)
  apply (div_le_div_of_nonneg_right hs (by nlinarith : 0 ≤ x ^ 2 - x)).trans
  rw [div_le_iff₀ (by nlinarith : 0 < x ^ 2 - x)]
  rw [show 3 * (1 + x ^ 2)⁻¹ * (x ^ 2 - x) =
      (3 * (x ^ 2 - x)) / (1 + x ^ 2) by field_simp]
  rw [le_div_iff₀ (by nlinarith [sq_nonneg x] : 0 < 1 + x ^ 2)]
  nlinarith [sq_nonneg x]

private lemma integrable_extension : Integrable apm_a96A08_extension volume := by
  apply continuous_extension.locallyIntegrable.integrable_of_isBigO_atBot_atTop
      (g := fun x : ℝ => (1 + x ^ 2)⁻¹) (g' := fun x : ℝ => (1 + x ^ 2)⁻¹)
  · refine Asymptotics.isBigO_iff.mpr ⟨3, ?_⟩
    filter_upwards [Filter.eventually_le_atBot (-2 : ℝ)] with x hx
    exact extension_bound_left hx
  · exact integrable_inv_one_add_sq.integrableAtFilter _
  · refine Asymptotics.isBigO_iff.mpr ⟨3, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    exact extension_bound_right hx
  · exact integrable_inv_one_add_sq.integrableAtFilter _

private lemma tendsto_sinc_affine_interval (c : ℝ) :
    Filter.Tendsto
      (fun R : ℝ => ∫ u in Real.pi * (-R - c)..Real.pi * (R - c), Real.sinc u)
      Filter.atTop (nhds Real.pi) := by
  have hright : Filter.Tendsto
      (fun R : ℝ => ∫ u in (0 : ℝ)..Real.pi * (R - c), Real.sinc u)
      Filter.atTop (nhds (Real.pi / 2)) := by
    apply ConstructionTargets.Sinc.tendsto_integral_sinc_pi_div_two.comp
    apply Filter.Tendsto.const_mul_atTop Real.pi_pos
    simpa [sub_eq_add_neg] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (-c) Filter.tendsto_id)
  have hleft : Filter.Tendsto
      (fun R : ℝ => ∫ u in Real.pi * (-R - c)..(0 : ℝ), Real.sinc u)
      Filter.atTop (nhds (Real.pi / 2)) := by
    have ht : Filter.Tendsto
        (fun R : ℝ => ∫ u in (0 : ℝ)..Real.pi * (R + c), Real.sinc u)
        Filter.atTop (nhds (Real.pi / 2)) := by
      apply ConstructionTargets.Sinc.tendsto_integral_sinc_pi_div_two.comp
      apply Filter.Tendsto.const_mul_atTop Real.pi_pos
      exact Filter.tendsto_atTop_add_const_right Filter.atTop c Filter.tendsto_id
    apply Filter.Tendsto.congr' _ ht
    filter_upwards with R
    have hneg := intervalIntegral.integral_comp_neg
      (f := Real.sinc) (a := (0 : ℝ)) (b := Real.pi * (R + c))
    have hneg' : (∫ x in (0 : ℝ)..Real.pi * (R + c), Real.sinc x) =
        ∫ x in -(Real.pi * (R + c))..(0 : ℝ), Real.sinc x := by
      simpa only [Real.sinc_neg, neg_zero] using hneg
    convert hneg' using 1
    all_goals ring_nf
  have hadd := hleft.add hright
  convert hadd using 1
  · funext R
    rw [intervalIntegral.integral_add_adjacent_intervals
      (Real.continuous_sinc.intervalIntegrable _ _)
      (Real.continuous_sinc.intervalIntegrable _ _)]
  · ring

private lemma tendsto_extension_integral :
    Filter.Tendsto
      (fun R : ℝ => ∫ x in Set.Icc (-R) R, apm_a96A08_extension x ∂volume)
      Filter.atTop (nhds (-(2 * Real.pi))) := by
  have h0 := tendsto_sinc_affine_interval 0
  have h1 := tendsto_sinc_affine_interval 1
  have hlim : Filter.Tendsto
      (fun R : ℝ => -((∫ u in Real.pi * (-R - 0)..Real.pi * (R - 0), Real.sinc u) +
        ∫ u in Real.pi * (-R - 1)..Real.pi * (R - 1), Real.sinc u))
      Filter.atTop (nhds (-(2 * Real.pi))) := by
    convert (h0.add h1).neg using 1
    all_goals ring_nf
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self hR)]
  unfold apm_a96A08_extension
  rw [intervalIntegral.integral_neg]
  have hi0 := intervalIntegral.smul_integral_comp_mul_sub
    (f := Real.sinc) (a := -R) (b := R) Real.pi 0
  have hi1 := intervalIntegral.smul_integral_comp_mul_sub
    (f := Real.sinc) (a := -R) (b := R) Real.pi Real.pi
  simp only [smul_eq_mul] at hi0 hi1
  have hi0' : Real.pi * (∫ x in -R..R, Real.sinc (Real.pi * x)) =
      ∫ u in Real.pi * (-R - 0)..Real.pi * (R - 0), Real.sinc u := by
    convert hi0 using 1 <;> ring
  have hi1' : Real.pi * (∫ x in -R..R, Real.sinc (Real.pi * (x - 1))) =
      ∫ u in Real.pi * (-R - 1)..Real.pi * (R - 1), Real.sinc u := by
    convert hi1 using 1 <;> ring
  have hia : IntervalIntegrable (fun x : ℝ => Real.sinc (Real.pi * x)) volume (-R) R := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hib : IntervalIntegrable
      (fun x : ℝ => Real.sinc (Real.pi * (x - 1))) volume (-R) R := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add hia hib]
  rw [mul_add, hi0', hi1']

theorem apm_a96a08 :
    Integrable apm_a96A08_integrand volume ∧
      (∫ x : ℝ, apm_a96A08_integrand x ∂volume) = -(2 * Real.pi) := by
  have hint : Integrable apm_a96A08_integrand volume :=
    integrable_extension.congr integrand_ae_eq_extension.symm
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae integrand_ae_eq_extension]
  exact (MeasureTheory.aecover_Icc
    Filter.tendsto_neg_atTop_atBot
    Filter.tendsto_id).integral_eq_of_tendsto _ integrable_extension
      tendsto_extension_integral
