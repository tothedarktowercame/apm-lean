import Mathlib

/-!
# APM a97A02 — continuity and bounds for sliding averages

## Statement repairs

None.

## Encoding questions

An `L^p([0,1])` function is represented by a measurable representative on
`ℝ` with `MemLp` for Lebesgue measure restricted to `Icc 0 1`. Consequently
the integral over `[t-h,t+h]` automatically uses the zero extension outside
`[0,1]`. The norm is Mathlib's `snorm` of that representative.
-/

open MeasureTheory Set

noncomputable section

def apm_a97A02_measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

def apm_a97A02_average (f : ℝ → ℂ) (h t : ℝ) : ℂ :=
  (∫ x in Set.Icc (t - h) (t + h), f x ∂apm_a97A02_measure) / (2 * h)

theorem apm_a97a02
    (p : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (f : ℝ → ℂ) (hf : MemLp f p apm_a97A02_measure)
    (h : ℝ) (hh : 0 < h) :
    ContinuousOn (apm_a97A02_average f h) (Set.Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖apm_a97A02_average f h t‖ ≤
        (2 * h) ^ (-(1 / p.toReal)) *
          (eLpNorm f p apm_a97A02_measure).toReal := by
  sorry
