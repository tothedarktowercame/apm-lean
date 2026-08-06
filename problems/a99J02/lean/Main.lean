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
  sorry
