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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
  sorry

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
