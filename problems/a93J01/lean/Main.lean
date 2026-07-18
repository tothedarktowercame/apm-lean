import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# APM a93J01: Continuous + BV + AC on [a,1] for all a > 0 ⟹ AC on [0,1]

**Problem.** Let f : [0,1] → ℝ be continuous, of bounded variation, and
absolutely continuous on [a,1] for all 0 < a < 1. Prove f is AC on [0,1].

## Proof

BV gives V(f, [0,a]) → 0 as a → 0⁺ (by `tendsto_eVariationOn_Icc_zero_left`).
Choose a₀ with V(f, [0,a₀]) < ε/2. Use AC on [a₀,1] to get δ > 0.
For any disjoint intervals with Σ(bᵢ-aᵢ) < min(δ, a₀):
- Intervals with aᵢ < a₀: total oscillation ≤ V(f, [0, 2a₀]) < ε/2
- Intervals with aᵢ ≥ a₀: handled by AC on [a₀,1], sum < ε/2
Total < ε.

## Statement repair note

Uses Mathlib's `AbsolutelyContinuousOnInterval` for AC, `BoundedVariationOn`
for BV, and `eVariationOn` for total variation. The informal proof's
custom `AbsolutelyContinuousOn` is replaced by Mathlib's definition.
-/

set_option linter.unusedVariables false in
noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace ApmCanaries.A93J01

/-- **Main theorem:** continuous + BV + AC on [a,1] for all 0 < a < 1
    implies AC on [0,1].

    **SORRY BOUNDARY:** The proof requires:
    (1) `BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left` gives
        V(f, [0,a]) → 0 as a → 0, using continuity at 0 + BV.
    (2) AC on [a₀,1] gives δ for ε/2 on disjoint intervals in [a₀,1].
    (3) Splitting disjoint intervals: those touching [0,a₀) contribute
        ≤ V(f, [0, 2a₀]) < ε/2; those in [a₀,1] contribute < ε/2 by AC.
    The splitting argument requires connecting `eVariationOn` to sums
    of absolute differences on disjoint sub-intervals, plus the
    `absolutelyContinuousOnInterval_iff` characterization for the ε-δ step.
    Tried approaches:
    - `eVariationOn.mono`: V(f, S) ≤ V(f, T) when S ⊆ T, used for
      bounding oscillations on subsets.
    - `AbsolutelyContinuousOnInterval.sub`: AC of fₙ - f from AC of both.
    The main difficulty is the combinatorial bookkeeping of the interval
    partition and connecting `eVariationOn` to the AC ε-δ definition. -/
theorem ac_on_01_of_continuous_bv_ac_from_a
    {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc (0:ℝ) 1))
    (hBV : BoundedVariationOn f (Icc (0:ℝ) 1))
    (hAC : ∀ a : ℝ, 0 < a → a < 1 → AbsolutelyContinuousOnInterval f a 1) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  sorry

end ApmCanaries.A93J01
