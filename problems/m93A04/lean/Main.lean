import Mathlib

/-!
# APM m93A04: differentiability of a nonlinear integral operator

## Statement repairs

None. The problem explicitly asks the solver to choose sufficient hypotheses;
we choose joint continuity of `K` and its second partial derivative, followed
by the uniform smallness hypothesis `|∂₂K| ≤ c < 1` for invertibility.

## Encoding questions

None. `C[0,1]` is encoded as Mathlib's continuous-map Banach space on the
closed interval subtype, and the integrals are Bochner integrals over that
subtype with its restricted Lebesgue measure.
-/

noncomputable section

open MeasureTheory Set

abbrev apm_m93A04_I := Set.Icc (0 : ℝ) 1
abbrev apm_m93A04_C := C(apm_m93A04_I, ℝ)

theorem apm_m93a04
    (K K₂ : ℝ → ℝ → ℝ)
    (hK : Continuous (Function.uncurry K))
    (hK₂ : Continuous (Function.uncurry K₂))
    (hpartial : ∀ t u : ℝ, HasDerivAt (K t) (K₂ t u) u)
    (c : ℝ) (hc_nonneg : 0 ≤ c) (hc : c < 1)
    (hsmall : ∀ t u : ℝ, |K₂ t u| ≤ c)
    (F : apm_m93A04_C → apm_m93A04_C)
    (hF : ∀ (x : apm_m93A04_C) (t : apm_m93A04_I),
      F x t = x t - ∫ s : apm_m93A04_I, K t.1 (x s))
    (D : apm_m93A04_C →
      (apm_m93A04_C →L[ℝ] apm_m93A04_C))
    (hD : ∀ (x h : apm_m93A04_C) (t : apm_m93A04_I),
      D x h t = h t - ∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s) :
    (∀ x : apm_m93A04_C, HasFDerivAt F (D x) x) ∧
    ∀ x : apm_m93A04_C, Function.Bijective (D x) := by
  sorry
