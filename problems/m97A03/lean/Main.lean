import Mathlib

/-!
# APM m97A03: A nonlinear integral equation

## Statement repairs

None.

## Encoding questions

None. The singular kernel is encoded exactly in a Lebesgue integral on
`[0,1]`. Its convention-dependent value at the single endpoint `s = 0` does
not affect the integral.
-/

open MeasureTheory Set

noncomputable section

def apm_m97A03_isSolution (lam : ℝ) (u : ℝ → ℝ) : Prop :=
  ContinuousOn u (Icc 0 1) ∧
  ∀ t ∈ Icc (0 : ℝ) 1,
    u t - lam * (∫ s in Icc (0 : ℝ) 1,
      Real.sqrt ((t + 3) / s) * Real.sin (t * u s)) = Real.exp t

theorem apm_m97a03
    (lam : ℝ) (hlam : |lam| < (1 / 4 : ℝ)) :
    ∃ u : ℝ → ℝ, apm_m97A03_isSolution lam u := by
  sorry
