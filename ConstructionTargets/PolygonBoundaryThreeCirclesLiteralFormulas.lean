import ConstructionTargets.PolygonBoundaryThreeLoopHomeomorphisms

noncomputable section

namespace ConstructionTargets.PolygonBoundaryThreeCirclesLiteralFormulas

open PointWedgeQuotient
open IntervalEndpointQuotientCircle
open PolygonBoundaryInducedQuotient
open PolygonBoundaryCircleRelations
open PolygonBoundaryCircleSource
open PolygonBoundaryThreeLoopMaps
open PolygonBoundaryThreeLoopHomeomorphisms
open ThreeEndpointLoopsHomeomorph
open Surfaces
open PolygonTorusCrosscapRelation
open StatementSurfaceModels

theorem n3BoundaryHomeomorphThreeCircles_threeLoops
    (x : ThreeEndpointLoops) :
    n3BoundaryHomeomorphThreeCircles (n3ThreeLoops x) =
      threeEndpointLoopsHomeomorphThreeCircles x := by
  change threeEndpointLoopsHomeomorphThreeCircles
      (n3ThreeLoopsHomeomorph.symm (n3ThreeLoops x)) = _
  rw [← n3ThreeLoopsHomeomorph_apply,
    n3ThreeLoopsHomeomorph.symm_apply_apply]

theorem torusCrosscapBoundaryHomeomorphThreeCircles_threeLoops
    (x : ThreeEndpointLoops) :
    torusCrosscapBoundaryHomeomorphThreeCircles
        (torusCrosscapThreeLoops x) =
      threeEndpointLoopsHomeomorphThreeCircles x := by
  change threeEndpointLoopsHomeomorphThreeCircles
      (torusCrosscapThreeLoopsHomeomorph.symm
        (torusCrosscapThreeLoops x)) = _
  rw [← torusCrosscapThreeLoopsHomeomorph_apply,
    torusCrosscapThreeLoopsHomeomorph.symm_apply_apply]

@[simp] theorem n3Boundary_first (t : Interval) :
    n3BoundaryHomeomorphThreeCircles
        (n3CircleQuotientMap (circleEdgePoint 0 (toUnitIcc t))) =
      quotientMap twoCirclesPoint 1 (.inl
        (quotientMap 1 1 (.inl
          (endpointQuotientHomeomorphCircle (intervalQuotientMap t))))) := by
  rw [← n3LoopA_mk]
  rw [← n3ThreeLoops_first]
  exact n3BoundaryHomeomorphThreeCircles_threeLoops _

@[simp] theorem n3Boundary_second (t : Interval) :
    n3BoundaryHomeomorphThreeCircles
        (n3CircleQuotientMap (circleEdgePoint 2 (toUnitIcc t))) =
      quotientMap twoCirclesPoint 1 (.inl
        (quotientMap 1 1 (.inr
          (endpointQuotientHomeomorphCircle (intervalQuotientMap t))))) := by
  rw [← n3LoopB_mk]
  rw [← n3ThreeLoops_second]
  exact n3BoundaryHomeomorphThreeCircles_threeLoops _

@[simp] theorem n3Boundary_third (t : Interval) :
    n3BoundaryHomeomorphThreeCircles
        (n3CircleQuotientMap (circleEdgePoint 4 (toUnitIcc t))) =
      quotientMap twoCirclesPoint 1 (.inr
        (endpointQuotientHomeomorphCircle (intervalQuotientMap t))) := by
  rw [← n3LoopC_mk]
  rw [← n3ThreeLoops_third]
  exact n3BoundaryHomeomorphThreeCircles_threeLoops _

@[simp] theorem torusCrosscapBoundary_first (t : Interval) :
    torusCrosscapBoundaryHomeomorphThreeCircles
        (torusCrosscapCircleQuotientMap
          (circleEdgePoint 0 (toUnitIcc t))) =
      quotientMap twoCirclesPoint 1 (.inl
        (quotientMap 1 1 (.inl
          (endpointQuotientHomeomorphCircle (intervalQuotientMap t))))) := by
  rw [← torusCrosscapLoopA_mk]
  rw [← torusCrosscapThreeLoops_first]
  exact torusCrosscapBoundaryHomeomorphThreeCircles_threeLoops _

@[simp] theorem torusCrosscapBoundary_second (t : Interval) :
    torusCrosscapBoundaryHomeomorphThreeCircles
        (torusCrosscapCircleQuotientMap
          (circleEdgePoint 1 (toUnitIcc t))) =
      quotientMap twoCirclesPoint 1 (.inl
        (quotientMap 1 1 (.inr
          (endpointQuotientHomeomorphCircle (intervalQuotientMap t))))) := by
  rw [← torusCrosscapLoopB_mk]
  rw [← torusCrosscapThreeLoops_second]
  exact torusCrosscapBoundaryHomeomorphThreeCircles_threeLoops _

@[simp] theorem torusCrosscapBoundary_third (t : Interval) :
    torusCrosscapBoundaryHomeomorphThreeCircles
        (torusCrosscapCircleQuotientMap
          (circleEdgePoint 4 (toUnitIcc t))) =
      quotientMap twoCirclesPoint 1 (.inr
        (endpointQuotientHomeomorphCircle (intervalQuotientMap t))) := by
  rw [← torusCrosscapLoopC_mk]
  rw [← torusCrosscapThreeLoops_third]
  exact torusCrosscapBoundaryHomeomorphThreeCircles_threeLoops _

end ConstructionTargets.PolygonBoundaryThreeCirclesLiteralFormulas
