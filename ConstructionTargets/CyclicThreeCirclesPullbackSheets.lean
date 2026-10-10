import ConstructionTargets.CirclePowerFiberCard
import ConstructionTargets.CyclicThreeCirclesPullbackCover
import ConstructionTargets.CoveringDegree

noncomputable section

namespace ConstructionTargets.CyclicThreeCirclesPullbackSheets

open ConstructionTargets.CoveringDegree
open ConstructionTargets.CyclicThreeCirclesCollapse
open ConstructionTargets.CyclicThreeCirclesPullbackCover
open ConstructionTargets.CirclePowerFiberCard

theorem pullback_isKSheeted (n : ℕ) [NeZero n] :
    IsKSheetedCover (projection n) n where
  isCoveringMap := covering n
  finite_fiber y := by
    letI : Finite ((circlePower n) ⁻¹' {collapse y}) := by
      change Finite {z : Circle // z ^ n = collapse y}
      exact circlePower_fiber_finite n (collapse y)
    change Finite
      (ConstructionTargets.LiteralCoveringPullback.projection
        (circlePower n) collapse ⁻¹' {y})
    exact Finite.of_injective
      (ConstructionTargets.LiteralCoveringPullback.fiberEquiv
        (circlePower n) collapse y)
      (ConstructionTargets.LiteralCoveringPullback.fiberEquiv
        (circlePower n) collapse y).injective
  card_fiber y := by
    change Nat.card
      (ConstructionTargets.LiteralCoveringPullback.projection
        (circlePower n) collapse ⁻¹' {y}) = n
    rw [ConstructionTargets.LiteralCoveringPullback.fiber_card]
    exact circlePower_fiber_card n (collapse y)

#print axioms pullback_isKSheeted

end ConstructionTargets.CyclicThreeCirclesPullbackSheets
