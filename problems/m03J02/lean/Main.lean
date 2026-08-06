import Mathlib

/-! # APM m03J02: global dynamics of `u' + u = cos u`

## Statement repairs

Part (b) calls the problem a “boundary value problem”; it is the initial value
problem from part (a), so the formal statement refers to the same IVP.
-/

open Filter

noncomputable section

/-- A global classical solution on the nonnegative time axis. -/
def IsM03J02Solution (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  u 0 = u₀ ∧ ∀ t : ℝ, 0 ≤ t → HasDerivAt u (Real.cos (u t) - u t) t

/-- Every initial value gives exactly one global solution, and all such
solutions converge to the same equilibrium. -/
theorem apm_m03j02 :
    (∀ u₀ : ℝ, ∃! u : ℝ → ℝ, IsM03J02Solution u₀ u) ∧
    (∃ ξ : ℝ, ∀ (u₀ : ℝ) (u : ℝ → ℝ),
      IsM03J02Solution u₀ u → Tendsto u atTop (nhds ξ)) := by
  sorry
