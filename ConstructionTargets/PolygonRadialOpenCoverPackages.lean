import ConstructionTargets.PolygonInnerOpenPointedContraction

open Set Topology
open unitInterval
noncomputable section

namespace ConstructionTargets.PolygonRadialOpenCoverPackages

open Surfaces
open PolygonRadialOpenCover
open PolygonOuterRadialRelation
open PolygonOuterOpenDeformation
open PolygonOverlapHomotopyEquivCircle
open PolygonBoundaryInducedQuotient
open PolygonBoundaryCircleRelations
open PolygonBoundaryThreeLoopHomeomorphisms
open PolygonBoundaryThreeCirclesLiteralFormulas
open PolygonBoundaryVertexClasses
open PolygonInnerOpenPointedContraction
open PolygonTorusCrosscapRelation
open PointedPuncturedCircleContraction
open StatementSurfaceModels

variable (R : Disk → Disk → Prop)

structure ConcretePackage
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) where
  cover : Package R hR
  innerContraction : PointedContraction (innerOpen R) (innerBase R)
  outerHomotopy : I × outerOpen R → outerOpen R
  outerHomotopy_continuous : Continuous outerHomotopy
  outerHomotopy_zero : ∀ z, outerHomotopy (0, z) = z
  outerHomotopy_one_boundary : ∀ z,
    IsBoundaryClass R hR (outerHomotopy (1, z))
  outerHomotopy_fixed : ∀ t z, IsBoundaryClass R hR z →
    outerHomotopy (t, z) = z
  overlapEquiv : ContinuousMap.HomotopyEquiv Circle (overlapOpen R)
  boundaryModel : CircleQuotient R ≃ₜ ThreeCircles

def concretePackage
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (boundaryModel : CircleQuotient R ≃ₜ ThreeCircles) :
    ConcretePackage R hR hboundary where
  cover := package R hR
  innerContraction := innerOpenPointedContraction R hR hboundary
  outerHomotopy := outerOpenHomotopy R hR hboundary
  outerHomotopy_continuous := continuous_outerOpenHomotopy R hR hboundary
  outerHomotopy_zero := outerOpenHomotopy_zero R hR hboundary
  outerHomotopy_one_boundary :=
    outerOpenHomotopy_one_boundary R hR hboundary
  outerHomotopy_fixed := outerOpenHomotopy_fixed R hR hboundary
  overlapEquiv := overlapHomotopyEquivCircle R hR hboundary
  boundaryModel := boundaryModel

def n3Radius : ∀ ⦃x y⦄, SurfaceRel false 3 x y → radius x = radius y :=
  fun {_ _} h => surfaceRel_radius_eq false 3 h

def n3Boundary : ∀ ⦃x y⦄, SurfaceRel false 3 x y →
    radius x = 1 ∧ radius y = 1 :=
  fun {_ _} h => surfaceRel_boundary false 3 h

def torusCrosscapRadius : ∀ ⦃x y⦄, TorusCrosscapRel x y →
    radius x = radius y :=
  fun {_ _} h => by simpa [radius] using torusCrosscapRel_norm_eq h

def torusCrosscapBoundary : ∀ ⦃x y⦄, TorusCrosscapRel x y →
    radius x = 1 ∧ radius y = 1 :=
  fun {_ _} h => torusCrosscapRel_boundary h

def n3Package : ConcretePackage (SurfaceRel false 3) n3Radius n3Boundary :=
  concretePackage _ n3Radius n3Boundary n3BoundaryHomeomorphThreeCircles

def torusCrosscapPackage :
    ConcretePackage TorusCrosscapRel torusCrosscapRadius torusCrosscapBoundary :=
  concretePackage _ torusCrosscapRadius torusCrosscapBoundary
    torusCrosscapBoundaryHomeomorphThreeCircles

def polygonRadialOpenCoverPackages :
    ConcretePackage (SurfaceRel false 3) n3Radius n3Boundary ×
      ConcretePackage TorusCrosscapRel torusCrosscapRadius
        torusCrosscapBoundary :=
  (n3Package, torusCrosscapPackage)

theorem package_vertex_classes :
    (∀ j : Fin 6, n3CircleQuotientMap (vertex j) =
      n3CircleQuotientMap (vertex 0)) ∧
    (∀ j : Fin 6, torusCrosscapCircleQuotientMap (vertex j) =
      torusCrosscapCircleQuotientMap (vertex 0)) :=
  ⟨n3_all_vertices, torusCrosscap_all_vertices⟩

end ConstructionTargets.PolygonRadialOpenCoverPackages
