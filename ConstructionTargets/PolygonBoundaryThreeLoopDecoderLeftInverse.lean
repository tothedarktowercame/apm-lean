import ConstructionTargets.PolygonBoundaryCircleDecoderRelationInvariant

open ConstructionTargets

noncomputable section

namespace ConstructionTargets.PolygonBoundaryThreeLoopDecoderLeftInverse

open PointWedgeQuotient
open IntervalEndpointQuotientCircle
open PolygonBoundaryCircleRelations
open PolygonBoundaryCircleDecoderWellDefined
open PolygonBoundaryCircleDecoderRelationInvariant
open PolygonBoundaryThreeLoopMaps
open PolygonBoundaryThreeLoopSurjectivityReduction
open PolygonBoundaryInducedQuotient
open PolygonThreeLoopHalfOpenNormalForm
open RelationQuotientLeftInverse
open ThreeEndpointLoopsHomeomorph
open PolygonTorusCrosscapRelation
open Surfaces

def n3QuotientDecode : CircleQuotient (SurfaceRel false 3) → ThreeEndpointLoops :=
  descend N3CircleRel n3CircleDecode (fun _ _ h => n3CircleDecode_respects h)

def torusCrosscapQuotientDecode : CircleQuotient TorusCrosscapRel → ThreeEndpointLoops :=
  descend TorusCrosscapCircleRel torusCrosscapCircleDecode
    (fun _ _ h => torusCrosscapCircleDecode_respects h)

theorem n3QuotientDecode_first (t : Interval) :
    n3QuotientDecode (n3ThreeLoops (firstLoopPoint t)) = firstLoopPoint t := by
  change n3CircleDecode (circleEdgePoint 0 (toUnitIcc t)) = _
  rw [n3CircleDecode_edge]
  rfl

theorem n3QuotientDecode_second (t : Interval) :
    n3QuotientDecode (n3ThreeLoops (secondLoopPoint t)) = secondLoopPoint t := by
  change n3CircleDecode (circleEdgePoint 2 (toUnitIcc t)) = _
  rw [n3CircleDecode_edge]
  rfl

theorem n3QuotientDecode_third (t : Interval) :
    n3QuotientDecode (n3ThreeLoops (thirdLoopPoint t)) = thirdLoopPoint t := by
  change n3CircleDecode (circleEdgePoint 4 (toUnitIcc t)) = _
  rw [n3CircleDecode_edge]
  rfl

theorem torusCrosscapQuotientDecode_first (t : Interval) :
    torusCrosscapQuotientDecode (torusCrosscapThreeLoops (firstLoopPoint t)) =
      firstLoopPoint t := by
  change torusCrosscapCircleDecode (circleEdgePoint 0 (toUnitIcc t)) = _
  rw [torusCrosscapCircleDecode_edge]
  rfl

theorem torusCrosscapQuotientDecode_second (t : Interval) :
    torusCrosscapQuotientDecode (torusCrosscapThreeLoops (secondLoopPoint t)) =
      secondLoopPoint t := by
  change torusCrosscapCircleDecode (circleEdgePoint 1 (toUnitIcc t)) = _
  rw [torusCrosscapCircleDecode_edge]
  rfl

theorem torusCrosscapQuotientDecode_third (t : Interval) :
    torusCrosscapQuotientDecode (torusCrosscapThreeLoops (thirdLoopPoint t)) =
      thirdLoopPoint t := by
  change torusCrosscapCircleDecode (circleEdgePoint 4 (toUnitIcc t)) = _
  rw [torusCrosscapCircleDecode_edge]
  rfl

theorem n3QuotientDecode_leftInverse :
    Function.LeftInverse n3QuotientDecode n3ThreeLoops := by
  intro x
  rcases threeEndpointLoops_halfOpen_rep x with
    ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact n3QuotientDecode_first _
  · exact n3QuotientDecode_second _
  · exact n3QuotientDecode_third _

theorem torusCrosscapQuotientDecode_leftInverse :
    Function.LeftInverse torusCrosscapQuotientDecode torusCrosscapThreeLoops := by
  intro x
  rcases threeEndpointLoops_halfOpen_rep x with
    ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact torusCrosscapQuotientDecode_first _
  · exact torusCrosscapQuotientDecode_second _
  · exact torusCrosscapQuotientDecode_third _

#print axioms n3QuotientDecode_first
#print axioms torusCrosscapQuotientDecode_first
#print axioms n3QuotientDecode_leftInverse
#print axioms torusCrosscapQuotientDecode_leftInverse

end ConstructionTargets.PolygonBoundaryThreeLoopDecoderLeftInverse
