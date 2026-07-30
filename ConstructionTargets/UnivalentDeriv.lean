import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Derivative of a univalent holomorphic function

The target is the standard fact that a holomorphic function which is injective
on an open set has nonvanishing derivative there.

The local analytic-order reduction is recorded below.  The remaining
construction is the local-degree step: an analytic germ of order at least two
is not locally injective.
-/

open Set

noncomputable section

namespace ConstructionTargets.UnivalentDeriv

/-- If a complex analytic function has zero derivative at `z`, then
`g - g z` vanishes to order at least two at `z`. -/
lemma two_le_analyticOrderAt_sub_self
    {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)
    (hderiv : deriv g z = 0) :
    (2 : ℕ) ≤ analyticOrderAt (fun w => g w - g z) z := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hg.fun_sub analyticAt_const)]
  intro i hi
  interval_cases i
  · simp
  · simpa using hderiv

/-- A holomorphic function injective on an open set has nonzero derivative at
every point of that set. -/
theorem deriv_ne_zero_of_injOn
    {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hinj : InjOn g U)
    {z : ℂ} (hz : z ∈ U) :
    deriv g z ≠ 0 := by
  -- If `deriv g z = 0`, `two_le_analyticOrderAt_sub_self` shows that the
  -- centered germ has order at least two.  The missing local-degree lemma
  -- must then produce distinct `x,y` in every neighborhood of `z` with
  -- `g x = g y`, contradicting `hinj`.
  sorry

end ConstructionTargets.UnivalentDeriv
