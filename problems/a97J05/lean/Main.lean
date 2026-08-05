/-
! # APM a97J05: Taylor coefficients converge to minus the residue of the nearest pole

If f(z) is analytic on {|z|<2} except for a simple pole at z=1 with residue A,
and f(z) = Σa(n)zⁿ on {|z|<1}, prove lim a(n) = -A.

## Strategy (from informal-solution.md)

1. Define g(z) = f(z) - A/(z-1). The pole cancels, so g is analytic on {|z|<2}.
2. The geometric series A/(z-1) = -A·Σzⁿ on {|z|<1} contributes constant -A.
3. So b(n) = a(n) + A, where b(n) are g's Maclaurin coefficients.
4. Cauchy estimates: |b(n)| ≤ M(r)/rⁿ → 0 for any 1 < r < 2. Hence a(n) → -A.

## Phase-A hints used
-- (Memory: math-informal/estimate-by-bounding) Cauchy coefficient estimates are the key bound.
-- (Memory: e-codexpilot-package-closed-ball-holomorphicity-as-DiffContOnCl-for-Cauchy-estimates)
--    API guidance for packaging analyticity for Cauchy estimates.
-- (Memory: e-codexpilot-extend-a-reciprocal-across-finite-punctures-then-apply-Liouville)
--    Extending reciprocal across puncture: subtracting A/(z-1) removes the pole.

## Boundary

The proof requires:
1. Pole removal: g = f - A/(z-1) extends analytically to {|z|<2}.
2. Geometric series: 1/(z-1) = -Σzⁿ on {|z|<1}, coefficient extraction.
3. Cauchy estimates: coefficients of analytic function on {|z|<R} decay if R > 1.
4. Combining: a(n) + A = b(n) → 0.

APIs searched:
- `AnalyticAt`, `AnalyticOnNhd` — FOUND: `Analysis/Analytic/Basic.lean`
- `FormalMultilinearSeries.ofScalars`, `.coeff` — FOUND
- `HasFPowerSeriesOnBall` — FOUND
- Coefficient decay: need `FormalMultilinearSeries.radius` or related
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Complex.Basic

open Complex Filter Topology
open scoped Topology

noncomputable section

namespace APMa97J05

/-- Main theorem: if f has Maclaurin series Σa(n)zⁿ on {|z|<1}, and g = f - A/(z-1)
    is analytic on {|z| < 2}, then a(n) → -A.

    -- (Memory: math-informal/estimate-by-bounding) Cauchy estimates bound coefficients.
    -- (Memory: e-codexpilot-package-closed-ball-holomorphicity-as-DiffContOnCl-for-Cauchy-estimates)
    --    Package analyticity for the Cauchy bound.
    -- (Memory: e-codexpilot-extend-a-reciprocal-across-finite-punctures-then-apply-Liouville)
    --    Pole removal: g = f - A/(z-1) is analytic on the full disk. -/
theorem coeff_converges_to_neg_residue
    (f : ℂ → ℂ)
    (a : ℕ → ℂ)
    (A : ℂ)
    (hf_series : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hg_analytic : AnalyticOnNhd ℂ (fun z => f z - A / (z - 1))
      (Metric.eball (0 : ℂ) 2)) :
    Tendsto a atTop (𝓝 (-A)) := by
  sorry

#print axioms APMa97J05.coeff_converges_to_neg_residue

end APMa97J05
