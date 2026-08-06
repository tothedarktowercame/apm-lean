import Mathlib

/-!
# APM a98A07

## Statement repairs

None.

## Encoding questions

None.  “Uniformly on compact subsets” is represented by Mathlib's
`TendstoLocallyUniformlyOn` predicate.
-/

open Filter MeasureTheory Metric Set
open scoped Topology

theorem apm_a98a07 :
    ∀ f : ℕ → ℂ → ℂ,
      (∃ U : Set ℂ,
        IsOpen U ∧ closedBall (0 : ℂ) 1 ⊆ U ∧
          ∀ n : ℕ, DifferentiableOn ℂ (f n) U) →
      (∀ (n : ℕ) (t : ℝ), 0 < t → t < 2 * Real.pi →
        ‖f n (Complex.exp (Complex.I * (t : ℂ)))‖ ≤
          1 / (t * (Real.log (t / (4 * Real.pi))) ^ 2)) →
      (∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) (2 * Real.pi))),
        ∃ w : ℂ,
          Tendsto (fun n : ℕ => f n (Complex.exp (Complex.I * (t : ℂ)))) atTop (𝓝 w)) →
      ∃ g : ℂ → ℂ,
        DifferentiableOn ℂ g (ball 0 1) ∧
        TendstoLocallyUniformlyOn f g atTop (ball 0 1) := by
  -- SKIPPED: Vitali's convergence theorem for holomorphic functions.
  -- Requires: (1) local boundedness from the boundary estimate (integrability of
  --   1/(t·(log(t/4π))²)); (2) Cauchy integral formula reconstruction; (3) Vitali/Montel.
  -- -- (Memory: e-codexpilot-propagate-local-analytic-vanishing-across-a-connected-domain)
  --    tangentially relevant but about vanishing, not convergence.
  -- APIs: `DifferentiableOn`, `TendstoLocallyUniformlyOn`, `circleIntegral` — FOUND,
  --   but Vitali's theorem itself is NOT in Mathlib.
  sorry
