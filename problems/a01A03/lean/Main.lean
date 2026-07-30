import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# APM a01A03: Convolution identity determines indicator function

**Problem.** For `g ∈ L¹(ℝ)` and any `f ∈ C¹(ℝ)`, suppose that
`g ∗ f'(x) = f(x+h) - f(x-h)` for all x. Show that `g ≡ χ_{[-h,h]}`.

**Statement repair note.**

The informal-solution file `apm-a01A03.md` was harvested with the **wrong
content**: it contains the proof for a01A02 (weak-L² implies local L¹), not
a01A03 (convolution identity). The proposed Lean statements are for the
weak-L² problem. This file implements the correct problem from `a01A03.tex`.

**Proof sketch.**

Take the Fourier transform of both sides. Using the convolution theorem
(`F(g ∗ f') = ĝ · F(f')`) and the Fourier derivative rule
(`F(f') = iξ f̂(ξ)`):

  `ĝ(ξ) · iξ · f̂(ξ) = (e^{ihξ} - e^{-ihξ}) · f̂(ξ) = 2i sin(hξ) · f̂(ξ)`

Since this holds for all f ∈ C¹(ℝ), we need `ĝ(ξ) · iξ = 2i sin(hξ)`,
so `ĝ(ξ) = 2 sin(hξ) / ξ` for ξ ≠ 0.

The inverse Fourier transform of `2 sin(hξ) / ξ` is exactly `χ_{[-h,h]}`
(the indicator of the interval [-h, h]). This is the standard Fourier pair
for rectangular functions.

Hence `g = χ_{[-h,h]}`.

**Formalization route.**

The implemented proof avoids the missing Fourier pair. It subtracts
`χ_{[-h,h]}`, uses the fundamental theorem of calculus to show that this
difference annihilates derivatives of smooth compactly supported functions,
and convolves it with reflected test functions. The resulting convolution has
zero derivative and is therefore constant; integrability on `ℝ` forces that
constant to vanish. The fundamental lemma for distributions then gives the
required almost-everywhere equality.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory FourierTransform Filter ContinuousLinearMap Set

open scoped Convolution ContDiff

namespace ApmCanaries.A01A03

/-- **Main theorem.** If `g ∈ L¹(ℝ)` and `g ∗ f'(x) = f(x+h) - f(x-h)`
    for all `f ∈ C¹(ℝ)` and all `x`, then `g = χ_{[-h,h]}` (the indicator
    of the interval `[-h, h]`).

    The formal proof uses distributional uniqueness: after subtracting the
    interval indicator, convolution with any reflected test function has zero
    derivative and is integrable, hence vanishes. The fundamental lemma then
    identifies the difference with zero almost everywhere.
-/
-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). Two defects, both introduced in
-- translation; the informal solution had it right. See faithfulness-ledger #5.
--
-- (1) CONCLUSION was POINTWISE (`∀ x, g x = …`) while `hidentity` constrains `g`
--     only through integrals, i.e. only almost everywhere. Machine-checked
--     consequence: the old statement was EQUIVALENT to `hidentity` being
--     unsatisfiable — modify any witness at one point and integrals are
--     unchanged, so the modified function is another witness whose pointwise
--     conclusion fails. The informal solution says "g = χ_{[-h,h]} almost
--     everywhere", twice explicitly (lines 11 and 21). Now an a.e. equality.
--
--
-- (3) CORRECTION 2026-07-30, SAME DAY, TO REPAIR (2) ABOVE — the fault was mine.
--     Repair (2) was written as `ContDiff ℝ ⊤ f` intending SMOOTH. In the current
--     smoothness-index API the index is `WithTop ℕ∞` and `⊤ = ω` means REAL
--     ANALYTIC, strictly above `∞`. Mathlib's own ContDiff/Defs.lean says "For
--     n = ω, we require the function to be analytic". Since every compactly
--     supported real-analytic function on ℝ is identically zero, `hidentity` then
--     quantified over f = 0 ALONE and was vacuous: g = 0, h = 1 satisfies every
--     hypothesis and refutes the conclusion. So the repair introduced a NEW false
--     statement while fixing an old one. Found by codex-7 on durée run 2, which
--     committed the machine-checked refutation below rather than working around it.
--     Corrected to `ContDiff ℝ ∞`, the smooth test class actually intended.
-- (2) TEST CLASS was every differentiable `f`, with no requirement that `deriv f`
--     be integrable. A differentiable function can have a non-integrable
--     derivative, and Lean's Bochner integral of a non-integrable function is
--     0 — so `hidentity` demanded `0 = f (x+h) - f (x-h)` for such `f`, which no
--     `g` satisfies. Restricted to smooth compactly supported test functions,
--     the standard class for the Fourier/distributional argument the informal
--     solution actually uses.
theorem convolution_identity_implies_indicator
    (g : ℝ → ℝ) (hg1 : Integrable g volume)
    (h : ℝ) (hh : 0 < h)
    (hidentity : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∀ x : ℝ,
        (∫ t, g t * (deriv f) (x - t) ∂volume) = f (x + h) - f (x - h)) :
    g =ᵐ[volume] fun x => if x ∈ Set.Icc (-h) h then 1 else 0 := by
  let χ : ℝ → ℝ := (Icc (-h) h).indicator (fun _ => 1)
  let k : ℝ → ℝ := fun x => g x - χ x

  have hχ1 : Integrable χ volume := by
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-h) h) volume :=
      integrableOn_const (by simp)
    have hind :
        Integrable ((Icc (-h) h).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
      apply (hconst.indicator measurableSet_Icc).integrable_of_forall_notMem_eq_zero
      intro x hx
      simp [Set.indicator_of_notMem hx]
    exact hind

  have hk1 : Integrable k volume := hg1.sub hχ1

  have hχ_identity (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : ℝ) :
      (∫ t, χ t * deriv f (x - t) ∂volume) =
        f (x + h) - f (x - h) := by
    have hi :
        (fun t : ℝ => χ t * deriv f (x - t)) =
          (Icc (-h) h).indicator (fun t => deriv f (x - t)) := by
      funext t
      change
        (Icc (-h) h).indicator (fun _ => (1 : ℝ)) t * deriv f (x - t) =
          (Icc (-h) h).indicator (fun t => deriv f (x - t)) t
      by_cases ht : t ∈ Icc (-h) h
      · rw [indicator_of_mem ht, indicator_of_mem ht]
        simp
      · rw [indicator_of_notMem ht, indicator_of_notMem ht]
        simp
    rw [hi, integral_indicator measurableSet_Icc]
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by linarith : -h ≤ h)]
    rw [intervalIntegral.integral_comp_sub_left]
    convert intervalIntegral.integral_deriv_of_contDiffOn_uIcc
      (hf.of_le (by norm_num)).contDiffOn using 1 <;> ring_nf

  have hk_deriv_test_zero
      (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
      (x : ℝ) :
      (k ⋆ deriv f) x = 0 := by
    have hfd_cont : Continuous (deriv f) :=
      hf.continuous_deriv (by norm_num)
    have hfd_compact : HasCompactSupport (deriv f) := hfc.deriv
    have hg_int :
        Integrable (fun t => g t * deriv f (x - t)) volume :=
      (hfd_compact.convolutionExists_right (lsmul ℝ ℝ)
        hg1.locallyIntegrable hfd_cont x).integrable
    have hχ_int :
        Integrable (fun t => χ t * deriv f (x - t)) volume :=
      (hfd_compact.convolutionExists_right (lsmul ℝ ℝ)
        hχ1.locallyIntegrable hfd_cont x).integrable
    rw [show
      (k ⋆ deriv f) x =
        ∫ t, (g t * deriv f (x - t) - χ t * deriv f (x - t)) ∂volume by
          apply integral_congr_ae
          exact Eventually.of_forall fun t => by simp [k]]
    rw [integral_sub hg_int hχ_int, hidentity f hf hfc x, hχ_identity f hf x]
    ring

  have htest :
      ∀ (q : ℝ → ℝ), ContDiff ℝ ∞ q → HasCompactSupport q →
        ∫ x, q x • k x ∂volume = 0 := by
    intro q hq hqc
    let f : ℝ → ℝ := fun x => q (-x)
    have hf : ContDiff ℝ ∞ f := by
      simpa only [f, Function.comp_apply, id_eq] using hq.comp contDiff_id.neg
    have hfc : HasCompactSupport f := by
      simpa only [f, Function.comp_apply] using
        hqc.comp_homeomorph (Homeomorph.neg ℝ)
    have hf1 : Integrable f volume :=
      hf.continuous.integrable_of_hasCompactSupport hfc
    have hconv1 : Integrable (k ⋆ f) volume :=
      hk1.integrable_convolution (lsmul ℝ ℝ) hf1
    have hconv_deriv : ∀ x : ℝ, HasDerivAt (k ⋆ f) 0 x := by
      intro x
      convert hfc.hasDerivAt_convolution_right (lsmul ℝ ℝ)
        hk1.locallyIntegrable (hf.of_le (by norm_num)) x using 1
      exact (hk_deriv_test_zero f hf hfc x).symm
    have hconv_const : k ⋆ f = fun _ => (k ⋆ f) 0 := by
      funext x
      exact is_const_of_deriv_eq_zero
        (fun y => (hconv_deriv y).differentiableAt)
        (fun y => (hconv_deriv y).deriv) x 0
    have hconst1 : Integrable (fun _ : ℝ => (k ⋆ f) 0) volume := by
      rw [← hconv_const]
      exact hconv1
    have hconv_zero : (k ⋆ f) 0 = 0 := by
      rcases integrable_const_iff.mp hconst1 with hzero | hfinite
      · exact hzero
      · exact False.elim
          ((not_isFiniteMeasure_iff.mpr Real.volume_univ) hfinite)
    simpa only [convolution_def, f, zero_sub, neg_neg, lsmul_apply,
      smul_eq_mul, mul_comm] using hconv_zero

  have hk_zero : k =ᵐ[volume] (0 : ℝ → ℝ) :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hk1.locallyIntegrable htest
  filter_upwards [hk_zero] with x hx
  by_cases hxI : x ∈ Icc (-h) h
  · simpa [χ, indicator_of_mem hxI, hxI] using sub_eq_zero.mp hx
  · simpa [χ, indicator_of_notMem hxI, hxI] using sub_eq_zero.mp hx

/-- In the current smoothness-index API, `ContDiff ℝ ⊤` means real analytic
(`ContDiff ℝ ω`), not merely infinitely differentiable (`ContDiff ℝ ∞`).
Consequently a compactly supported function satisfying the former is zero. -/
theorem analytic_compactSupport_eq_zero
    (f : ℝ → ℝ) (hf : ContDiff ℝ ω f) (hfc : HasCompactSupport f) :
    f = 0 := by
  have hf_an : AnalyticOnNhd ℝ f univ := hf.analyticOnNhd
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z ∉ tsupport f := by
    by_contra hn
    push_neg at hn
    exact hfc.ne_univ (eq_univ_of_forall hn)
  apply hf_an.eq_of_eventuallyEq
    (analyticOnNhd_const : AnalyticOnNhd ℝ (fun _ : ℝ => (0 : ℝ)) univ)
  filter_upwards [(isOpen_compl_iff.mpr (isClosed_tsupport f)).mem_nhds hz] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- The hypotheses of `convolution_identity_implies_indicator` are satisfied by
`g = 0`, because its analytic compactly supported test class contains only the
zero function, while its conclusion fails for every `h > 0`. -/
theorem convolution_identity_counterexample :
    ∃ (g : ℝ → ℝ) (h : ℝ),
      Integrable g volume ∧ 0 < h ∧
      (∀ f : ℝ → ℝ, ContDiff ℝ ⊤ f → HasCompactSupport f →
        ∀ x : ℝ,
          (∫ t, g t * (deriv f) (x - t) ∂volume) = f (x + h) - f (x - h)) ∧
      ¬(g =ᵐ[volume] fun x => if x ∈ Set.Icc (-h) h then 1 else 0) := by
  refine ⟨(0 : ℝ → ℝ), (1 : ℝ), integrable_zero ℝ ℝ volume, zero_lt_one, ?_, ?_⟩
  · intro f hf hfc x
    have hf0 : f = 0 := analytic_compactSupport_eq_zero f hf hfc
    simp [hf0]
  · intro hae
    have hae' :
        (0 : ℝ → ℝ) =ᵐ[volume]
          (Icc (-1) 1).indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [hae] with x hx
      by_cases hxI : x ∈ Icc (-1) 1
      · simpa [indicator_of_mem hxI, hxI] using hx
      · simpa [indicator_of_notMem hxI, hxI] using hx
    have hint :
        ∫ x : ℝ, (Icc (-1) 1).indicator (fun _ => (1 : ℝ)) x ∂volume = 0 := by
      simpa using (integral_congr_ae hae').symm
    have hz : volume.real (Icc (-1 : ℝ) 1) = 0 := by
      simpa using hint
    norm_num [Measure.real, Real.volume_Icc] at hz

end ApmCanaries.A01A03
