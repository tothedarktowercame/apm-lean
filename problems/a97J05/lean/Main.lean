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
  /-
  CLOSER HOP 1 boundary (2026-08-05).

  Consulted `problems/a96J09/lean/Main.lean`: the compiled theorem
  `apm_a96J09_coeff_tendsto_zero_of_contains_closed_disk` proves precisely
  that normalized iterated derivatives tend to zero when a function is
  analytic on an open set containing the closed unit disk.  Its proof uses
  `DiffContOnCl.diffContOnCl_ball` and
  `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`; this can be
  reused locally for `g z = f z - A / (z - 1)` on the radius-two ball.

  Consulted Mathlib `Analysis/Analytic/Constructions.lean`: the geometric
  series is packaged as `formalMultilinearSeries_geometric`, with
  `formalMultilinearSeries_geometric_eq_ofScalars` and
  `hasFPowerSeriesOnBall_inverse_one_sub`. Thus the polar part has the
  `ofScalars` coefficients constantly `-A` after rewriting
  `A / (z - 1) = -A * (1 - z)⁻¹`.

  Consulted Mathlib `Analysis/Calculus/IteratedDeriv/Defs.lean` and
  `Analysis/Analytic/Uniqueness.lean`: `AnalyticAt.hasFPowerSeriesAt`
  supplies coefficients `iteratedDeriv n g 0 / n!`, while
  `HasFPowerSeriesAt.eq_formalMultilinearSeries` identifies them with the
  series obtained by subtracting the geometric polar series from
  `hf_series`.

  The remaining integration is import/API elaboration: construct the scaled
  geometric `HasFPowerSeriesAt`, use `.sub` and uniqueness to prove
  `iteratedDeriv n g 0 / n! = a n + A`, apply the a96J09 Cauchy-decay proof,
  and finish by subtraction of the constant sequence. Searches of a01J04 and
  a96A06 found only informal or still-sorry variants, so they were discarded
  as compiled dependencies. No statement defect was found, and no claim is
  made that this bridge is unroutable.
  -/
  sorry

#print axioms APMa97J05.coeff_converges_to_neg_residue

end APMa97J05
