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

/-- Coordinate zero is the endpoint integer of the lifted left projection
of an explicit based product loop. -/
theorem torusPi1Coord_mk_apply_zero_eq_liftEndpoint
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    (torusPi1Coord (Path.Homotopic.Quotient.mk gamma)).toAdd 0 =
      liftBasedLoopEndpointInteger
        (gamma.map continuous_fst) (gamma.map continuous_fst).source
          (gamma.map continuous_fst).target := by
  change (circleFundamentalGroupMulEquivInt
      (Path.Homotopic.projLeft (Path.Homotopic.Quotient.mk gamma))).toAdd = _
  rw [show Path.Homotopic.projLeft (Path.Homotopic.Quotient.mk gamma) =
      Path.Homotopic.Quotient.mk (gamma.map continuous_fst) by
    exact (Path.Homotopic.Quotient.mk_map gamma ⟨Prod.fst, continuous_fst⟩).symm]
  rfl

/-- Coordinate one is the endpoint integer of the lifted right projection
of an explicit based product loop. -/
theorem torusPi1Coord_mk_apply_one_eq_liftEndpoint
    (gamma : Path ((1 : Circle), (1 : Circle)) (1, 1)) :
    (torusPi1Coord (Path.Homotopic.Quotient.mk gamma)).toAdd 1 =
      liftBasedLoopEndpointInteger
        (gamma.map continuous_snd) (gamma.map continuous_snd).source
          (gamma.map continuous_snd).target := by
  change (circleFundamentalGroupMulEquivInt
      (Path.Homotopic.projRight (Path.Homotopic.Quotient.mk gamma))).toAdd = _
  rw [show Path.Homotopic.projRight (Path.Homotopic.Quotient.mk gamma) =
      Path.Homotopic.Quotient.mk (gamma.map continuous_snd) by
    exact (Path.Homotopic.Quotient.mk_map gamma ⟨Prod.snd, continuous_snd⟩).symm]
  rfl

end ConstructionTargets.TorusPiOneWindingCoordinates
