import ConstructionTargets.PolygonBoundaryThreeLoopMaps

noncomputable section

namespace ConstructionTargets.PolygonBoundaryThreeLoopContinuity

open Topology
open PointWedgeQuotient
open PolygonBoundaryCircleRelations
open PolygonBoundaryInducedQuotient
open PolygonBoundaryThreeLoopMaps
open ThreeEndpointLoopsHomeomorph
open IntervalEndpointQuotientCircle
open Surfaces
open PolygonTorusCrosscapRelation
open PolygonBoundaryCircleSource

theorem continuous_toUnitIcc : Continuous toUnitIcc := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem continuous_circleEdgePoint (j : Fin 6) :
    Continuous (circleEdgePoint j) := by
  apply boundaryCircleHomeomorph.symm.continuous.comp
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  fun_prop

theorem continuous_wedgeLift {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x₀ : X} {y₀ : Y} (f : X → Z) (g : Y → Z)
    (hbase : f x₀ = g y₀) (hf : Continuous f) (hg : Continuous g) :
    Continuous (wedgeLift f g hbase) := by
  unfold wedgeLift
  apply Continuous.quotient_lift
  rw [continuous_sum_dom]
  exact ⟨hf, hg⟩

theorem continuous_n3Loop (j : Fin 6)
    (hend : n3CircleQuotientMap (circleEdgePoint j
        PolygonBoundaryVertexClasses.zeroIcc) =
      n3CircleQuotientMap (circleEdgePoint j
        PolygonBoundaryVertexClasses.oneIcc)) :
    Continuous (n3Loop j hend) := by
  apply continuous_quot_lift
  exact continuous_coinduced_rng.comp
    ((continuous_circleEdgePoint j).comp continuous_toUnitIcc)

theorem continuous_n3LoopA : Continuous n3LoopA :=
  continuous_n3Loop _ _

theorem continuous_n3LoopB : Continuous n3LoopB :=
  continuous_n3Loop _ _

theorem continuous_n3LoopC : Continuous n3LoopC :=
  continuous_n3Loop _ _

theorem continuous_n3TwoLoops : Continuous n3TwoLoops :=
  continuous_wedgeLift _ _ _ continuous_n3LoopA continuous_n3LoopB

theorem continuous_n3ThreeLoops : Continuous n3ThreeLoops :=
  continuous_wedgeLift _ _ _ continuous_n3TwoLoops continuous_n3LoopC

theorem continuous_torusCrosscapLoop (j : Fin 6)
    (hend : torusCrosscapCircleQuotientMap (circleEdgePoint j
        PolygonBoundaryVertexClasses.zeroIcc) =
      torusCrosscapCircleQuotientMap (circleEdgePoint j
        PolygonBoundaryVertexClasses.oneIcc)) :
    Continuous (torusCrosscapLoop j hend) := by
  apply continuous_quot_lift
  exact continuous_coinduced_rng.comp
    ((continuous_circleEdgePoint j).comp continuous_toUnitIcc)

theorem continuous_torusCrosscapLoopA : Continuous torusCrosscapLoopA :=
  continuous_torusCrosscapLoop _ _

theorem continuous_torusCrosscapLoopB : Continuous torusCrosscapLoopB :=
  continuous_torusCrosscapLoop _ _

theorem continuous_torusCrosscapLoopC : Continuous torusCrosscapLoopC :=
  continuous_torusCrosscapLoop _ _

theorem continuous_torusCrosscapTwoLoops : Continuous torusCrosscapTwoLoops :=
  continuous_wedgeLift _ _ _ continuous_torusCrosscapLoopA
    continuous_torusCrosscapLoopB

theorem continuous_torusCrosscapThreeLoops : Continuous torusCrosscapThreeLoops :=
  continuous_wedgeLift _ _ _ continuous_torusCrosscapTwoLoops
    continuous_torusCrosscapLoopC

end ConstructionTargets.PolygonBoundaryThreeLoopContinuity
