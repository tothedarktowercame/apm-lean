import ConstructionTargets.CyclicThreeCirclesCollapse
import ConstructionTargets.LiteralCoveringPullback

open ConstructionTargets
open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.CyclicThreeCirclesCollapse

noncomputable section

namespace ConstructionTargets.CyclicThreeCirclesPullbackCover

def circlePower (n : ℕ) : Circle → Circle := fun z => z ^ n

theorem continuous_circlePower (n : ℕ) : Continuous (circlePower n) := by
  exact continuous_pow n

abbrev Pullback (n : ℕ) :=
  LiteralCoveringPullback.Pullback (circlePower n) collapse

def projection (n : ℕ) : Pullback n → ThreeCircles :=
  LiteralCoveringPullback.projection (circlePower n) collapse

theorem covering (n : ℕ) [NeZero n] : IsCoveringMap (projection n) := by
  exact LiteralCoveringPullback.covering
    (Circle.isQuotientCoveringMap_npow n).isCoveringMap continuous_collapse

theorem projection_apply (n : ℕ) (z : Pullback n) : projection n z = z.1.1 := rfl

#print axioms continuous_circlePower
#print axioms covering
#print axioms projection_apply

end ConstructionTargets.CyclicThreeCirclesPullbackCover
