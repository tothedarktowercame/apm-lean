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
  -- Boundary (closer hop 2): still open. Enriched analysis of tractability.
  --
  -- Attempted to close conjuncts (1) and (2) separately:
  --
  -- (1) ∫⁻ g < ⊤: The lintegral of the ENNReal-valued derivative series.
  --     Key issue: `apmDerivativeSeries` has an if-then-else branch:
  --       g(x) = ∑ ENNReal.ofReal(deriv(fₙ)(x)) if all fₙ differentiable at x, else 0.
  --     The "all differentiable" condition is stronger than needed; for AC functions
  --     on [0,1], each fₙ is differentiable a.e. But the universal quantifier
  --     `∀ n, DifferentiableAt` makes the if-branch very hard to reason about.
  --     Specifically: Tonelli requires measurability of g, which requires showing
  --     the set {x : ∀ n, DifferentiableAt ℝ (f n) x} is measurable.
  --     This is a countable intersection of measurable sets (each fₙ is AC ⟹ differentiable a.e.
  --     ⟹ the set of differentiability points is measurable). But assembling this
  --     in Lean is non-trivial.
  --     Blocker: the `if ∀ n, DifferentiableAt` guard in `apmDerivativeSeries` makes
  --     measurability and Tonelli exchange very hard to prove formally.
  --
  -- (2) g < ⊤ a.e.: depends on (1).
  --
  -- (3) deriv(f) = g a.e.: same deep blocker as before (Stieltjes measure pipeline).
  --
  -- New consultation: Mathlib `MeasureTheory.Function.AEqFun` for differentiability
  --   of AC functions a.e. — discarded: AC ⟹ differentiable a.e. is available but
  --   doesn't directly help with the `∀ n, DifferentiableAt` guard.
  --
  -- Assessment: the encoding via `if ∀ n, DifferentiableAt` is the root difficulty.
  -- If g were simply ∑ ENNReal.ofReal(max(deriv(fₙ)(x), 0)), the proof would be
  -- much more tractable. But the statement is frozen and cannot be changed.
  sorry
