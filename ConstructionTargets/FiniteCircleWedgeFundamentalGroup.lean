import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.TwoOpenFreeProductMapping
import ConstructionTargets.CircleUniversalCover

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace ConstructionTargets.FiniteCircleWedgeFundamentalGroup

/-- The canonical wedge point in the two-circle model. -/
def twoBase : TwoCircles := quotientMap 1 1 (.inl 1)

/-- The canonical wedge point in the three-circle model. -/
def threeBase : ThreeCircles :=
  quotientMap twoCirclesPoint 1 (.inl twoCirclesPoint)

/-- The first representative circle in `TwoCircles`. -/
def twoLeft (z : Circle) : TwoCircles := quotientMap 1 1 (.inl z)

/-- The second representative circle in `TwoCircles`. -/
def twoRight (z : Circle) : TwoCircles := quotientMap 1 1 (.inr z)

/-- The old two-circle summand in `ThreeCircles`. -/
def threeOld (z : TwoCircles) : ThreeCircles :=
  quotientMap twoCirclesPoint 1 (.inl z)

/-- The new circle summand in `ThreeCircles`. -/
def threeNew (z : Circle) : ThreeCircles :=
  quotientMap twoCirclesPoint 1 (.inr z)

@[simp] theorem twoLeft_base : twoLeft 1 = twoBase := rfl

@[simp] theorem twoRight_base : twoRight 1 = twoBase := by
  exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm

@[simp] theorem threeOld_base : threeOld twoCirclesPoint = threeBase := rfl

@[simp] theorem threeNew_base : threeNew 1 = threeBase := by
  exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm

#print axioms twoRight_base
#print axioms threeNew_base

end ConstructionTargets.FiniteCircleWedgeFundamentalGroup
