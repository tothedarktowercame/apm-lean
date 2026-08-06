import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a99J02

## Statement repairs

The source's `E \leq [0,1]` is read as the intended set containment
`E \subseteq [0,1]`; numerical order between a set and an interval is ill-typed.

## Encoding notes

`apmTranslate E t` is exactly the image `{x+t | x ∈ E}`, and
`apmIndicatorConvolution` is the displayed Lebesgue integral on all of `ℝ`.
-/

def apmIndicator (E : Set ℝ) : ℝ → ℝ :=
  E.indicator (fun _ ↦ 1)

noncomputable def apmIndicatorConvolution (E : Set ℝ) (x : ℝ) : ℝ :=
  ∫ y, apmIndicator E (x - y) * apmIndicator E y ∂volume

def apmTranslate (E : Set ℝ) (t : ℝ) : Set ℝ :=
  (fun x ↦ x + t) '' E

theorem apm_a99j02
    {E : Set ℝ}
    (hE_measurable : MeasurableSet E)
    (hE_interval : E ⊆ Icc (0 : ℝ) 1)
    (hE_positive : 0 < volume E) :
    Continuous (apmIndicatorConvolution E) ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, |t| < ε → 0 < volume (E ∩ apmTranslate E t) := by
  -- SKIPPED: two-part problem.
  -- (a) χ_E * χ_E is continuous: follows from L¹ translation continuity
  --   (χ_E ∈ L¹ on [0,1], convolution with L¹ kernel is continuous).
  --   Key API: `integral_translate_norm` or `Continuous.convolution` type lemmas.
  -- (b) ∃ε>0: m(E∩(E+t))>0 for |t|<ε. Since χ_E*χ_E(t) = m(E∩(E+t)) (up to sign),
  --   continuity from (a) + (χ_E*χ_E)(0) = m(E) > 0 ⟹ positive near 0.
  -- Blocker: Mathlib's convolution continuity needs the right form for
  -- indicator functions; the identity χ_E*χ_E(t) = m(E∩(E+t)) requires careful setup.
  -- APIs: `Continuous.convolution_integrand`, `MeasureTheory.Measure.inter_measure`,
  --   `MeasureTheory.Function.UniformIntegrable`, `tendsto_measure_inter`
  sorry
