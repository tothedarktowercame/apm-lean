import ConstructionTargets.FundamentalGroupProduct
import ConstructionTargets.CircleUniversalCover
import ConstructionTargets.TwiceSpiralH1Coordinates

noncomputable section
namespace ConstructionTargets.TorusPiOneWindingCoordinates

open ConstructionTargets.FundamentalGroupProduct
open ConstructionTargets.CircleUniversalCover
open ConstructionTargets.TwiceSpiralH1Coordinates

/-- The two endpoint-winding coordinates on the based fundamental group of
the product torus. -/
def torusPi1Coord :
    FundamentalGroup (Circle × Circle) (1, 1) ≃*
      Multiplicative (Fin 2 → ℤ) :=
  (fundamentalGroupProdMulEquiv (1 : Circle) (1 : Circle)).trans
    ((circleFundamentalGroupMulEquivInt.prodCongr
      circleFundamentalGroupMulEquivInt).trans
        ((MulEquiv.prodMultiplicative ℤ ℤ).symm.trans
          intProdMulEquivFinTwo))

@[simp] theorem torusPi1Coord_apply_zero
    (p : FundamentalGroup (Circle × Circle) (1, 1)) :
    (torusPi1Coord p).toAdd 0 =
      (circleFundamentalGroupMulEquivInt (Path.Homotopic.projLeft p)).toAdd := by
  rfl

@[simp] theorem torusPi1Coord_apply_one
    (p : FundamentalGroup (Circle × Circle) (1, 1)) :
    (torusPi1Coord p).toAdd 1 =
      (circleFundamentalGroupMulEquivInt (Path.Homotopic.projRight p)).toAdd := by
  rfl

end ConstructionTargets.TorusPiOneWindingCoordinates
