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

/-- The countable differentiability guard in `apmDerivativeSeries` holds almost
everywhere on the interval.  Thus the guard itself does not lose any mass. -/
lemma apm_a94a02_ae_all_differentiable
    (f : ℕ → ℝ → ℝ)
    (hf_ac : ∀ n, AbsolutelyContinuousOnInterval (f n) 0 1) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∀ n, DifferentiableAt ℝ (f n) x := by
  rw [ae_restrict_iff' measurableSet_Icc]
  have h_all : ∀ᵐ x ∂volume, ∀ n,
      x ∈ uIcc (0 : ℝ) 1 → DifferentiableAt ℝ (f n) x := by
    exact ae_all_iff.2 fun n => (hf_ac n).ae_differentiableAt
  filter_upwards [h_all] with x hx hxi
  exact fun n => hx n (by simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hxi)

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
  -- Boundary (closer hop 3): still open, but the guarded branch is now resolved a.e.
  --
  -- Attempted to close conjuncts (1) and (2) separately:
  --
  -- (1) ∫⁻ g < ⊤: The lintegral of the ENNReal-valued derivative series.
  --     Key issue: `apmDerivativeSeries` has an if-then-else branch:
  --       g(x) = ∑ ENNReal.ofReal(deriv(fₙ)(x)) if all fₙ differentiable at x, else 0.
  --     The new proved helper `apm_a94a02_ae_all_differentiable` closes this issue:
  --     `AbsolutelyContinuousOnInterval.ae_differentiableAt` and `ae_all_iff`
  --     assemble the countable intersection directly on the restricted measure.
  --
  -- (2) g < ⊤ a.e.: depends on (1).
  --
  -- (3) deriv(f) = g a.e.: `LEMMA-INDEX.md` exposed the fully proved sibling
  --     `APM.deriv_sum_of_monotone_ae` in `a01J03`.  Its Stieltjes/Radon--Nikodym
  --     argument proves exactly derivative-of-series interchange for globally
  --     monotone functions with pointwise summability.  Here monotonicity is only
  --     on `Icc 0 1`.  A viable route is to replace each term by
  --     `x ↦ f n (max 0 (min 1 x))`, apply the sibling globally, and transfer the
  --     derivative equality back on `Ioo 0 1`; the endpoints are null.  Completing
  --     this requires the clamp map's monotonicity, pointwise summability (using
  --     `0 ≤ f n x ≤ f n 1`), and local derivative congruence for both each term
  --     and the tsum.  Those localization lemmas remain unproved in this hop.
  --
  -- Mathlib source additionally checked:
  -- `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` supplies the exact
  -- per-term integral identity, and
  -- `lintegral_deriv_eq_volume_image_of_monotoneOn` supplies a set-local
  -- monotone derivative formula, but the latter requires differentiability at
  -- every point and therefore does not directly replace the sibling's a.e.
  -- Stieltjes argument.
  sorry
