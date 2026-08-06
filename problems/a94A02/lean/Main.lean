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
  -- Boundary (enriched by closer hop 1):
  -- Three conjuncts all blocked by deep measure-theoretic assembly.
  --
  -- (1) ∫⁻ g < ⊤: Need to show the lintegral of the derivative series is finite.
  --     Key: by Tonelli, ∫⁻ g = ∑⁻ ∫ |f_n'| ≤ ∑ (f_n(1) - f_n(0)) ≤ ∑ f_n(1) < ∞.
  --     For AC functions: ∫₀¹ |f_n'| = f_n(1) - f_n(0) (since f_n monotone ⟹ f_n' ≥ 0).
  --     API: `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`, `lintegral_tsum`
  --     Consulted LEMMA-INDEX.md: `ac_integral_deriv_eq_sub` exists (a95A02, LusinN).
  --     Blocker: connecting AC integral identity to the ENNReal lintegral setup.
  --
  -- (2) g < ⊤ a.e.: Follows from (1) by `ae_lt_top_of_lintegral_ne_top`.
  --     API: confirmed available in Mathlib.
  --
  -- (3) deriv(f) = g a.e.: the deepest part. Requires monotone convergence of
  --     derivatives: ∂(∑f_n)/∂x = ∑ f_n' a.e. for monotone AC f_n with summable series.
  --     Consulted: `deriv_sum_of_monotone` in a01J03 — proves this for Monotone fns
  --     via Stieltjes measures and Lebesgue decomposition. Very sophisticated (120+ lines).
  --     Could potentially adapt, but the a01J03 proof uses `Monotone` not `MonotoneOn`
  --     and `AbsolutelyContinuousOnInterval`, and the encoding via ENNReal.ofReal
  --     differs significantly. Adaptation would require substantial rewriting.
  --     Blocker: the full Stieltjes measure decomposition pipeline is not reusable
  --     directly for this encoding.
  sorry
