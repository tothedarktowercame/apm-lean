import Mathlib

/-!
# APM a97J05: Coefficients controlled by a simple pole

## Statement repairs

None.

## Encoding questions

None. The generic complex-analysis API in this Mathlib build does not expose a
standalone residue function, so “simple pole with residue `A`” is defined by
its exact local Laurent principal part: `A ≠ 0` and
`f(z) = A/(z-z₀) + g(z)` punctured-locally for an analytic `g`. This retains
both pole order one and the residue rather than replacing either by a weaker
surrogate.
-/

open Filter Metric Set Topology

noncomputable section

/-- `f` has a pole of order one at `z₀`, with residue `A`. -/
def apm_a97J05_hasSimplePoleWithResidue
    (f : ℂ → ℂ) (z₀ A : ℂ) : Prop :=
  A ≠ 0 ∧ ∃ g : ℂ → ℂ,
    AnalyticAt ℂ g z₀ ∧
      ∀ᶠ z in 𝓝[≠] z₀, f z = A / (z - z₀) + g z

theorem apm_a97j05
    (f : ℂ → ℂ) (A : ℂ) (a : ℕ → ℂ)
    (hanalytic : AnalyticOn ℂ f (ball 0 2 \ ({1} : Set ℂ)))
    (hpole : apm_a97J05_hasSimplePoleWithResidue f 1 A)
    (hseries : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun n : ℕ => a n * z ^ n) (f z)) :
    Tendsto a atTop (𝓝 (-A)) := by
  sorry
