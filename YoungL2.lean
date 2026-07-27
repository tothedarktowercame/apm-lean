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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convolution

open MeasureTheory Set Filter

open scoped ENNReal

noncomputable section

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
  sorry

end
