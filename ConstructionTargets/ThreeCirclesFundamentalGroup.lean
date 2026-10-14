import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.FiniteCircleWedgeFundamentalGroup
import ConstructionTargets.CircleUniversalCover

/-!
# Fundamental group of the three-circle wedge

This is blueprint node B12.  It applies the literal-leg point-wedge
equivalence first to the inner two circles and then to the outer third
circle, before changing each circle coordinate to a rank-one free group.
-/

open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.FiniteCircleWedgeFundamentalGroup

noncomputable section

namespace ConstructionTargets.PointWedgeVanKampen

/-- The standard circle fundamental group in rank-one free-group
coordinates. -/
noncomputable def circleFundamentalGroupEquivFreeGroupFinOne :
    FundamentalGroup Circle 1 ≃* FreeGroup (Fin 1) :=
  ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.trans
    multiplicativeIntEquivFreeGroupFinOne

/-- The inner two-circle wedge in rank-two free-group coordinates. -/
noncomputable def twoCirclesFundamentalGroupEquiv :
    FundamentalGroup TwoCircles twoCirclesPoint ≃* FreeGroup (Fin 2) :=
  (genericPointWedgeLegCoordinatesEquiv
      (1 : Circle) (1 : Circle)
      circleBaseNeighborhood circleBaseNeighborhood
      circleBaseNeighborhood_isOpen circleBaseNeighborhood_isOpen
      circleBase_mem circleBase_mem
      circleBaseNeighborhood_contraction circleBaseNeighborhood_contraction).trans
    ((MulEquiv.coprodCongr circleFundamentalGroupEquivFreeGroupFinOne
        circleFundamentalGroupEquivFreeGroupFinOne).trans
      ((coprodFreeGroupEquivFreeGroupSum (Fin 1) (Fin 1)).trans
        (MulEquiv.ofBijective (FreeGroup.map finSumFinEquiv)
          ⟨FreeGroup.map_injective finSumFinEquiv.injective,
            FreeGroup.map_surjective finSumFinEquiv.surjective⟩)))

/-- B12: the fundamental group of the literal three-circle model is free of
rank three. -/
noncomputable def threeCirclesFundamentalGroupEquiv :
    FundamentalGroup ThreeCircles threeBase ≃* FreeGroup (Fin 3) :=
  (genericPointWedgeLegCoordinatesEquiv
      twoCirclesPoint (1 : Circle)
      circleBaseNeighborhood twoCirclesBaseNeighborhood
      circleBaseNeighborhood_isOpen twoCirclesBaseNeighborhood_isOpen
      circleBase_mem twoCirclesBase_mem
      circleBaseNeighborhood_contraction
      twoCirclesBaseNeighborhood_contraction).trans
    ((MulEquiv.coprodCongr twoCirclesFundamentalGroupEquiv
        circleFundamentalGroupEquivFreeGroupFinOne).trans
      coprodFreeGroupFinTwoFinOne_equiv)

#print axioms circleFundamentalGroupEquivFreeGroupFinOne
#print axioms twoCirclesFundamentalGroupEquiv
#print axioms threeCirclesFundamentalGroupEquiv

end ConstructionTargets.PointWedgeVanKampen
