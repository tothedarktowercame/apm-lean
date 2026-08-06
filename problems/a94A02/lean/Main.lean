import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a94A02

## Statement repairs

None. The referenced `informal-solution.md` is absent from this problem bundle, so
the TeX statement alone was used as the contract.

## Encoding notes

The source's one-based sequence is reindexed by `ℕ`. The derivative sum `g` takes
values in `ENNReal`, honestly retaining the possible value `+∞`; its integrability
is therefore stated as finiteness of its `lintegral`. The equality with `f'` uses
`ENNReal.ofReal`, justified mathematically by monotonicity.
-/

noncomputable def apmFunctionSeries (f : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, f n x

noncomputable def apmDerivativeSeries (f : ℕ → ℝ → ℝ) (x : ℝ) : ENNReal := by
  classical
  exact if ∀ n, DifferentiableAt ℝ (f n) x then
    ∑' n, ENNReal.ofReal (deriv (f n) x)
  else 0

theorem apm_a94a02
    (f : ℕ → ℝ → ℝ)
    (hf_monotone : ∀ n, MonotoneOn (f n) (Icc (0 : ℝ) 1))
    (hf_ac : ∀ n, AbsolutelyContinuousOnInterval (f n) 0 1)
    (hf_nonnegative : ∀ n x, x ∈ Icc (0 : ℝ) 1 → 0 ≤ f n x)
    (hf_sum : Summable (fun n ↦ f n 1)) :
    (∫⁻ x in Icc (0 : ℝ) 1, apmDerivativeSeries f x ∂volume) < ⊤ ∧
      (∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
        apmDerivativeSeries f x < ⊤) ∧
      (∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
        ENNReal.ofReal (deriv (apmFunctionSeries f) x) =
          apmDerivativeSeries f x) := by
  sorry
