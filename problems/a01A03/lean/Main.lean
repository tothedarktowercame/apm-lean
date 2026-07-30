import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Analytic.Uniqueness

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

**Formalization status.**

The proof requires:
1. The Fourier transform of L¹ convolutions (`fourier_convolution`).
2. The Fourier derivative rule for C¹ functions.
3. The specific Fourier transform of `χ_{[-h,h]}` being `2 sin(hξ)/ξ`.
4. Injectivity of the Fourier transform on L¹.

Each piece is standard in Fourier analysis but requires substantial
Mathlib infrastructure for the Fourier transform on L¹ functions with
the right hypotheses. The main theorem is stated correctly; the proof
is left as a documented sorry.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory FourierTransform Filter Set

open scoped ContDiff

namespace ApmCanaries.A01A03

/-- **Main theorem.** If `g ∈ L¹(ℝ)` and `g ∗ f'(x) = f(x+h) - f(x-h)`
    for all `f ∈ C¹(ℝ)` and all `x`, then `g = χ_{[-h,h]}` (the indicator
    of the interval `[-h, h]`).

    **SORRY BOUNDARY:** The proof uses the Fourier transform to convert the
    convolution equation into a pointwise identity `ĝ(ξ) = 2sin(hξ)/ξ`,
    then applies the inverse Fourier transform. This requires:
    (1) The convolution theorem for L¹ Fourier transforms.
    (2) The Fourier derivative rule.
    (3) The specific Fourier pair χ_{[-h,h]} ↔ 2sin(hξ)/ξ.
    (4) Injectivity of the L¹ Fourier transform.
    These are standard but the combined formalization in Mathlib requires
    careful management of integrability and differentiability hypotheses.
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
    (hidentity : ∀ f : ℝ → ℝ, ContDiff ℝ ⊤ f → HasCompactSupport f →
      ∀ x : ℝ,
        (∫ t, g t * (deriv f) (x - t) ∂volume) = f (x + h) - f (x - h)) :
    g =ᵐ[volume] fun x => if x ∈ Set.Icc (-h) h then 1 else 0 := by
  sorry

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
