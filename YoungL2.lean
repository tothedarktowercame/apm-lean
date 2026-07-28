/-
! # Young's convolution inequality (L² case)

If g ∈ L¹(μ) with ∫|g| ∂μ ≤ 1 and f ∈ L²(μ), then
the convolution (g * f)(x) = ∫ g(x-y) f(y) dy satisfies ‖g * f‖₂ ≤ ‖g‖₁ · ‖f‖₂.

For the heat kernel with ∫G_t = 1 and G_t ≥ 0, this gives ‖G_t * f‖₂ ≤ ‖f‖₂.

The proof uses:
1. Cauchy-Schwarz with the measure |g(x-y)| dy:
   |∫ g(x-y) f(y) dy|² ≤ (∫ |g(x-y)| dy)(∫ |g(x-y)| |f(y)|² dy)
2. Translation invariance of Lebesgue measure: ∫ |g(x-y)| dy = ∫ |g| = ‖g‖₁
3. Fubini: ∫∫ |g(x-y)| |f(y)|² dy dx = ‖g‖₁ · ‖f‖₂²

This file provides the formal statement and partial proof.
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Convolution

open MeasureTheory Set Filter

open scoped ENNReal

noncomputable section

/-- Translation by a fixed real number preserves the `ℒ²` seminorm.

This is one of the two concrete invariance inputs needed by the integral
Minkowski route to Young's inequality. -/
lemma eLpNorm_two_sub_right {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (y : ℝ) :
    eLpNorm (fun x => f (x - y)) 2 volume = eLpNorm f 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  simpa [sub_eq_add_neg] using
    lintegral_add_right_eq_self (μ := volume)
      (fun x => ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal) (-y)

/-- Weighted Cauchy--Schwarz in the nonnegative extended reals. -/
lemma lintegral_weight_mul_sq_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (w v : α → ℝ≥0∞) (hw : AEMeasurable w μ) (hv : AEMeasurable v μ) :
    (∫⁻ x, w x * v x ∂μ) ^ 2 ≤
      (∫⁻ x, w x ∂μ) * (∫⁻ x, w x * v x ^ 2 ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    Real.HolderConjugate.two_two
      (f := fun x => (w x) ^ (1 / 2 : ℝ))
      (g := fun x => (w x) ^ (1 / 2 : ℝ) * v x)
      (hw.pow_const _)
      ((hw.pow_const _).mul hv)
  simp only [Pi.mul_apply] at h
  have hhalf : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  have htwice : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  simp_rw [← mul_assoc,
    ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num),
    hhalf, ENNReal.rpow_one] at h
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul, htwice, ENNReal.rpow_one] at h
  have hsquare (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc
    (∫⁻ x, w x * v x ∂μ) ^ 2
        ≤ (((∫⁻ x, w x ∂μ) ^ (1 / 2 : ℝ)) *
          ((∫⁻ x, w x * v x ^ 2 ∂μ) ^ (1 / 2 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (zero_le _) h 2
    _ = (∫⁻ x, w x ∂μ) * (∫⁻ x, w x * v x ^ 2 ∂μ) := by
      rw [mul_pow, hsquare, hsquare]
      simp

/-- **Young's convolution inequality (L² case)**:

    If g ∈ L¹ and f ∈ L², then ‖g * f‖₂ ≤ ‖g‖₁ · ‖f‖₂.

    In particular, if ‖g‖₁ = 1 (e.g. a probability density like the heat kernel),
    then convolution with g is a contraction on L².

    **Proof strategy:** Weighted Cauchy-Schwarz + Fubini.
    |(g*f)(x)|² = |∫ g(x-y) f(y) dy|²
                ≤ (∫ |g(x-y)| dy)(∫ |g(x-y)| |f(y)|² dy)   [Cauchy-Schwarz]
                = ‖g‖₁ · ∫ |g(x-y)| |f(y)|² dy               [translation invariance]
    Integrating over x and using Fubini:
    ‖g*f‖₂² ≤ ‖g‖₁ · ∫ |f(y)|² (∫ |g(x-y)| dx) dy = ‖g‖₁² · ‖f‖₂². -/
theorem young_convolution_inequality_L2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → ℝ} {f : ℝ → E}
    (hg_int : Integrable g volume)
    (hf_lp : MemLp f 2 volume) :
    eLpNorm (fun x => ∫ y, g (x - y) • f y ∂volume) 2 volume ≤
      (ENNReal.ofReal (∫ y, ‖g y‖ ∂volume)) * eLpNorm f 2 volume := by
  have hpoint (x : ℝ) :
      ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ 2 ≤
        (∫⁻ y, ‖g y‖ₑ ∂volume) *
          (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) := by
    have hg_x : AEMeasurable (fun y : ℝ => ‖g (x - y)‖ₑ) volume :=
      ((hg_int.aestronglyMeasurable.comp_measurePreserving
        (Measure.measurePreserving_sub_left (volume : Measure ℝ) x)).enorm)
    have hf_enorm : AEMeasurable (fun y : ℝ => ‖f y‖ₑ) volume :=
      hf_lp.aestronglyMeasurable.enorm
    have hnorm :
        ‖∫ y, g (x - y) • f y ∂volume‖ₑ ≤
          ∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ∂volume := by
      refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
      apply lintegral_congr
      intro y
      simp [enorm_smul]
    calc
      ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ 2
          ≤ (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ∂volume) ^ 2 :=
        pow_le_pow_left₀ (zero_le _) hnorm 2
      _ ≤ (∫⁻ y, ‖g (x - y)‖ₑ ∂volume) *
          (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) :=
        lintegral_weight_mul_sq_le _ _ hg_x hf_enorm
      _ = (∫⁻ y, ‖g y‖ₑ ∂volume) *
          (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) := by
        congr 1
        let mp := Measure.measurePreserving_sub_left (volume : Measure ℝ) x
        have hg_comp : Integrable (fun t => g (x - t)) volume := by
          simpa [Function.comp_def] using mp.integrable_comp_of_integrable hg_int
        rw [← ofReal_integral_norm_eq_lintegral_enorm hg_comp,
          ← ofReal_integral_norm_eq_lintegral_enorm hg_int]
        congr 1
        exact integral_sub_left_eq_self (fun y => ‖g y‖) (volume : Measure ℝ) x
  let G : ℝ≥0∞ := ∫⁻ y, ‖g y‖ₑ ∂volume
  let F2 : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ^ 2 ∂volume
  have hG_top : G ≠ ∞ := by
    exact ne_of_lt hg_int.hasFiniteIntegral
  have h_joint : AEMeasurable
      (Function.uncurry fun x y : ℝ =>
        ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2)
      (volume.prod volume) := by
    have hg_joint : AEMeasurable
        (fun z : ℝ × ℝ => ‖g (z.1 - z.2)‖ₑ)
        (volume.prod volume) := by
      simpa [Function.comp_def] using
        (hg_int.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub (volume : Measure ℝ) volume))
    exact hg_joint.mul (hf_lp.aestronglyMeasurable.enorm.comp_snd.pow_const _)
  have hdouble :
      (∫⁻ x, ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ 2 ∂volume) ≤
        G ^ 2 * F2 := by
    calc
      (∫⁻ x, ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ 2 ∂volume)
          ≤ ∫⁻ x, G *
              (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) ∂volume := by
            apply lintegral_mono
            intro x
            exact hpoint x
      _ = G * (∫⁻ x,
              (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) ∂volume) := by
            rw [lintegral_const_mul' G _ hG_top]
      _ = G * (∫⁻ y,
              (∫⁻ x, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) ∂volume) := by
            rw [lintegral_lintegral_swap h_joint]
      _ = G * (G * F2) := by
            congr 1
            calc
              (∫⁻ y, (∫⁻ x, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) ∂volume)
                  = ∫⁻ y, G * ‖f y‖ₑ ^ 2 ∂volume := by
                    apply lintegral_congr
                    intro y
                    rw [lintegral_mul_const' _ _ (by finiteness)]
                    congr 1
                    simpa [G, sub_eq_add_neg] using
                      lintegral_add_right_eq_self (μ := volume)
                        (fun x => ‖g x‖ₑ) (-y)
              _ = G * F2 := by
                    rw [lintegral_const_mul' G _ hG_top]
      _ = G ^ 2 * F2 := by ring
  have hroot :
      (∫⁻ x, ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ (2 : ℝ) ∂volume) ^
          (1 / 2 : ℝ) ≤
        G * F2 ^ (1 / 2 : ℝ) := by
    calc
      (∫⁻ x, ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ (2 : ℝ) ∂volume) ^
            (1 / 2 : ℝ)
          ≤ (G ^ 2 * F2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (by simpa [ENNReal.rpow_two] using hdouble) (by norm_num)
      _ = G * F2 ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        congr 1
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    ofReal_integral_norm_eq_lintegral_enorm hg_int]
  simpa [G, F2] using hroot

/-- **Corollary: L² contraction for probability kernels.**

    If g ≥ 0 and ∫ g = 1, then ‖g * f‖₂ ≤ ‖f‖₂. -/
theorem convolution_L2_contraction_of_probability_kernel
    {g f : ℝ → ℝ}
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_int : ∫ x, g x ∂volume = 1)
    (hf_lp : MemLp f 2 volume) :
    eLpNorm (fun x => ∫ y, g (x - y) * f y ∂volume) 2 volume ≤
      eLpNorm f 2 volume := by
  have hg_integrable : Integrable g volume := by
    by_contra h
    have hg_zero : ∫ x, g x ∂volume = 0 := integral_undef h
    linarith [hg_int, hg_zero]
  have hg_abs : ∫ x, |g x| ∂volume = 1 := by
    simpa [abs_of_nonneg (hg_nonneg _)] using hg_int
  have hyoung := young_convolution_inequality_L2
    (E := ℝ) (g := g) (f := f) hg_integrable hf_lp
  simpa [smul_eq_mul, hg_abs] using hyoung

end
