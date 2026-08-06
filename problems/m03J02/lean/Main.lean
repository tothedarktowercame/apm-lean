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
  /-
  SKIPPED (frozen-statement defect). `IsM03J02Solution` constrains `u 0` and
  imposes the differential equation only at times `t ≥ 0`, but the first
  conjunct asserts uniqueness of functions of type `ℝ → ℝ` using global
  equality.

  Given any solution `u`, define `v` to equal `u` on `[-1, ∞)` and alter it
  arbitrarily on `(-∞, -1)` (for example add `1` there). Then `v 0 = u 0`, and
  for every `t ≥ 0` the functions agree on a neighborhood of `t`, so all the
  same `HasDerivAt` conditions hold. Thus both satisfy
  `IsM03J02Solution u₀`, while they are not equal as global functions. This
  refutes the asserted `∃!` independently of the standard ODE existence proof.

  The intended repair is to use functions on the subtype `Ici 0`, assert
  uniqueness with `Set.EqOn` on `Ici 0`, or require the ODE on all of `ℝ`.
  The statement is frozen, so no repair was made.
  -/
  sorry
