import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv

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

open MeasureTheory FourierTransform Filter

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
theorem convolution_identity_implies_indicator
    (g : ℝ → ℝ) (hg1 : Integrable g volume)
    (h : ℝ) (hh : 0 < h)
    (hidentity : ∀ f : ℝ → ℝ, Differentiable ℝ f →
      ∀ x : ℝ,
        (∫ t, g t * (deriv f) (x - t) ∂volume) = f (x + h) - f (x - h)) :
    ∀ x : ℝ, g x = if x ∈ Set.Icc (-h) h then 1 else 0 := by
  sorry

end ApmCanaries.A01A03
