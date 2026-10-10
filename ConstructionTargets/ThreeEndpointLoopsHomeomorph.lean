import ConstructionTargets.IntervalEndpointQuotientCircle
import ConstructionTargets.TorusCircleWedgeOpenCover
import ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace ConstructionTargets.ThreeEndpointLoopsHomeomorph

open PointWedgeQuotient
open IntervalEndpointQuotientCircle
open StatementSurfaceModels
open TorusCircleWedgeOpenCover

def endpointBase : EndpointQuotient :=
  intervalQuotientMap ⟨0, by norm_num⟩

abbrev TwoEndpointLoops := Wedge endpointBase endpointBase

def twoEndpointLoopsPoint : TwoEndpointLoops :=
  quotientMap endpointBase endpointBase (.inl endpointBase)

abbrev ThreeEndpointLoops := Wedge twoEndpointLoopsPoint endpointBase

def twoEndpointLoopsHomeomorphTwoCircles : TwoEndpointLoops ≃ₜ TwoCircles :=
  pointedWedgeHomeomorph endpointQuotientHomeomorphCircle
    endpointQuotientHomeomorphCircle
    endpointQuotientHomeomorphCircle_zero
    endpointQuotientHomeomorphCircle_zero

@[simp] theorem twoEndpointLoopsHomeomorphTwoCircles_base :
    twoEndpointLoopsHomeomorphTwoCircles twoEndpointLoopsPoint = twoCirclesPoint := by
  rw [twoEndpointLoopsHomeomorphTwoCircles, twoEndpointLoopsPoint,
    pointedWedgeHomeomorph_left]
  simp [twoCirclesPoint, endpointBase]

def threeEndpointLoopsHomeomorphThreeCircles :
    ThreeEndpointLoops ≃ₜ ThreeCircles :=
  pointedWedgeHomeomorph twoEndpointLoopsHomeomorphTwoCircles
    endpointQuotientHomeomorphCircle
    twoEndpointLoopsHomeomorphTwoCircles_base
    endpointQuotientHomeomorphCircle_zero

@[simp] theorem threeEndpointLoopsHomeomorphThreeCircles_left
    (x : TwoEndpointLoops) :
    threeEndpointLoopsHomeomorphThreeCircles
        (quotientMap twoEndpointLoopsPoint endpointBase (.inl x)) =
      quotientMap twoCirclesPoint 1
        (.inl (twoEndpointLoopsHomeomorphTwoCircles x)) := by
  rfl

@[simp] theorem threeEndpointLoopsHomeomorphThreeCircles_right
    (x : EndpointQuotient) :
    threeEndpointLoopsHomeomorphThreeCircles
        (quotientMap twoEndpointLoopsPoint endpointBase (.inr x)) =
      quotientMap twoCirclesPoint 1
        (.inr (endpointQuotientHomeomorphCircle x)) := by
  rfl

@[simp] theorem threeEndpointLoopsHomeomorphThreeCircles_first
    (x : EndpointQuotient) :
    threeEndpointLoopsHomeomorphThreeCircles
        (quotientMap twoEndpointLoopsPoint endpointBase
          (.inl (quotientMap endpointBase endpointBase (.inl x)))) =
      quotientMap twoCirclesPoint 1
        (.inl (quotientMap 1 1 (.inl (endpointQuotientHomeomorphCircle x)))) := by
  rfl

@[simp] theorem threeEndpointLoopsHomeomorphThreeCircles_second
    (x : EndpointQuotient) :
    threeEndpointLoopsHomeomorphThreeCircles
        (quotientMap twoEndpointLoopsPoint endpointBase
          (.inl (quotientMap endpointBase endpointBase (.inr x)))) =
      quotientMap twoCirclesPoint 1
        (.inl (quotientMap 1 1 (.inr (endpointQuotientHomeomorphCircle x)))) := by
  rfl

end ConstructionTargets.ThreeEndpointLoopsHomeomorph
