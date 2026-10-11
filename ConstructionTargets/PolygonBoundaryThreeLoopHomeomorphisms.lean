import ConstructionTargets.PolygonBoundaryCompactHausdorffInstances

noncomputable section

namespace ConstructionTargets.PolygonBoundaryThreeLoopHomeomorphisms

open PolygonBoundaryInducedQuotient
open PolygonBoundaryCircleRelations
open PolygonBoundaryThreeLoopMaps
open PolygonBoundaryThreeLoopContinuity
open PolygonBoundaryThreeLoopBijections
open PolygonBoundaryCompactHausdorffInstances
open ThreeEndpointLoopsHomeomorph
open Surfaces
open PolygonTorusCrosscapRelation
open StatementSurfaceModels

def n3ThreeLoopsHomeomorph :
    ThreeEndpointLoops ≃ₜ CircleQuotient (SurfaceRel false 3) := by
  letI : CompactSpace ThreeEndpointLoops :=
    polygonBoundaryCompactHausdorffInstances.1
  letI : T2Space (CircleQuotient (SurfaceRel false 3)) :=
    polygonBoundaryCompactHausdorffInstances.2.1
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective n3ThreeLoops bijective_n3ThreeLoops)
    continuous_n3ThreeLoops

def torusCrosscapThreeLoopsHomeomorph :
    ThreeEndpointLoops ≃ₜ CircleQuotient TorusCrosscapRel := by
  letI : CompactSpace ThreeEndpointLoops :=
    polygonBoundaryCompactHausdorffInstances.1
  letI : T2Space (CircleQuotient TorusCrosscapRel) :=
    polygonBoundaryCompactHausdorffInstances.2.2
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective torusCrosscapThreeLoops
      bijective_torusCrosscapThreeLoops)
    continuous_torusCrosscapThreeLoops

def n3BoundaryHomeomorphThreeCircles :
    CircleQuotient (SurfaceRel false 3) ≃ₜ ThreeCircles :=
  n3ThreeLoopsHomeomorph.symm.trans
    threeEndpointLoopsHomeomorphThreeCircles

def torusCrosscapBoundaryHomeomorphThreeCircles :
    CircleQuotient TorusCrosscapRel ≃ₜ ThreeCircles :=
  torusCrosscapThreeLoopsHomeomorph.symm.trans
    threeEndpointLoopsHomeomorphThreeCircles

@[simp] theorem n3ThreeLoopsHomeomorph_apply (x : ThreeEndpointLoops) :
    n3ThreeLoopsHomeomorph x = n3ThreeLoops x := rfl

@[simp] theorem torusCrosscapThreeLoopsHomeomorph_apply
    (x : ThreeEndpointLoops) :
    torusCrosscapThreeLoopsHomeomorph x = torusCrosscapThreeLoops x := rfl

theorem polygonBoundaryThreeLoopHomeomorphisms :
    Nonempty (ThreeEndpointLoops ≃ₜ
      CircleQuotient (SurfaceRel false 3)) ∧
    Nonempty (ThreeEndpointLoops ≃ₜ CircleQuotient TorusCrosscapRel) :=
  ⟨⟨n3ThreeLoopsHomeomorph⟩, ⟨torusCrosscapThreeLoopsHomeomorph⟩⟩

#print axioms polygonBoundaryThreeLoopHomeomorphisms

end ConstructionTargets.PolygonBoundaryThreeLoopHomeomorphisms
