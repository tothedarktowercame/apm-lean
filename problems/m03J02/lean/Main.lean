import Mathlib

/-! # APM m03J02: global dynamics of `u' + u = cos u`

## Statement repairs

Part (b) calls the problem a “boundary value problem”; it is the initial value
problem from part (a), so the formal statement refers to the same IVP.
-/

open Filter

noncomputable section

/-- A global classical solution on the whole real time axis.

The ODE is imposed at every `t : ℝ` (not only `t ≥ 0`) so that solutions are
unique as functions `ℝ → ℝ`; constraining only the nonnegative half-axis
would leave the past values free and refute the `∃!` conjunct. -/
def IsM03J02Solution (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  u 0 = u₀ ∧ ∀ t : ℝ, HasDerivAt u (Real.cos (u t) - u t) t

/-- Every initial value gives exactly one global solution, and all such
solutions converge to the same equilibrium. -/
theorem apm_m03j02 :
    (∀ u₀ : ℝ, ∃! u : ℝ → ℝ, IsM03J02Solution u₀ u) ∧
    (∃ ξ : ℝ, ∀ (u₀ : ℝ) (u : ℝ → ℝ),
      IsM03J02Solution u₀ u → Tendsto u atTop (nhds ξ)) := by
  /-
  Repaired statement (guide repair 1). The original imposed the ODE only for
  `t ≥ 0`, so two functions agreeing on `[-1, ∞)` but differing on `(-∞, -1)`
  both satisfied the predicate, refuting the `∃!` conjunct. The repair
  imposes `HasDerivAt` at every real `t`, restoring uniqueness of solutions
  on `ℝ → ℝ`. Existence/uniqueness and convergence to the equilibrium
  `ξ` solving `cos ξ = ξ` remain the mathematical content to prove.
  -/
  sorry
