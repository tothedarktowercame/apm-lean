import ConstructionTargets.PolygonBoundaryInducedQuotient

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonBoundaryCircleRelations

open ConstructionTargets.Surfaces
open ConstructionTargets.RadialQuotientOpenSets
open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PolygonTorusCrosscapRelation
open ConstructionTargets.PolygonBoundaryCircleSource
open ConstructionTargets.PolygonBoundaryInducedQuotient

def boundaryEdgePoint (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) : Boundary :=
  ⟨edgePoint 6 j t, by simpa [radius] using norm_edgePoint 6 j t⟩

def circleEdgePoint (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) : Circle :=
  boundaryToCircle (boundaryEdgePoint j t)

@[simp] theorem circleToBoundary_circleEdgePoint
    (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    circleToBoundary (circleEdgePoint j t) = boundaryEdgePoint j t := by
  exact circleToBoundary_boundaryToCircle _

abbrev N3CircleRel := CircleRel (SurfaceRel false 3)
abbrev TorusCrosscapCircleRel := CircleRel TorusCrosscapRel

theorem n3_rel_a (t : Set.Icc (0 : ℝ) 1) :
    N3CircleRel (circleEdgePoint 0 t) (circleEdgePoint 1 t) := by
  change SurfaceRel false 3 _ _
  simp only [circleToBoundary_circleEdgePoint, boundaryEdgePoint]
  refine ⟨0, by norm_num, t, ?_, ?_⟩
  · congr
  · congr

theorem n3_rel_b (t : Set.Icc (0 : ℝ) 1) :
    N3CircleRel (circleEdgePoint 2 t) (circleEdgePoint 3 t) := by
  change SurfaceRel false 3 _ _
  simp only [circleToBoundary_circleEdgePoint, boundaryEdgePoint]
  refine ⟨1, by norm_num, t, ?_, ?_⟩
  · congr
  · congr

theorem n3_rel_c (t : Set.Icc (0 : ℝ) 1) :
    N3CircleRel (circleEdgePoint 4 t) (circleEdgePoint 5 t) := by
  change SurfaceRel false 3 _ _
  simp only [circleToBoundary_circleEdgePoint, boundaryEdgePoint]
  refine ⟨2, by norm_num, t, ?_, ?_⟩
  · congr
  · congr

theorem torusCrosscap_rel_a (t : Set.Icc (0 : ℝ) 1) :
    TorusCrosscapCircleRel (circleEdgePoint 0 t)
      (circleEdgePoint 2 (reverse t)) := by
  change TorusCrosscapRel _ _
  simpa only [circleToBoundary_circleEdgePoint, boundaryEdgePoint] using
    TorusCrosscapRel.a t

theorem torusCrosscap_rel_b (t : Set.Icc (0 : ℝ) 1) :
    TorusCrosscapCircleRel (circleEdgePoint 1 t)
      (circleEdgePoint 3 (reverse t)) := by
  change TorusCrosscapRel _ _
  simpa only [circleToBoundary_circleEdgePoint, boundaryEdgePoint] using
    TorusCrosscapRel.b t

theorem torusCrosscap_rel_c (t : Set.Icc (0 : ℝ) 1) :
    TorusCrosscapCircleRel (circleEdgePoint 4 t) (circleEdgePoint 5 t) := by
  change TorusCrosscapRel _ _
  simpa only [circleToBoundary_circleEdgePoint, boundaryEdgePoint] using
    TorusCrosscapRel.c t

def n3CircleQuotientMap : Circle → CircleQuotient (SurfaceRel false 3) :=
  fun z => Quotient.mk _ z

def torusCrosscapCircleQuotientMap : Circle → CircleQuotient TorusCrosscapRel :=
  fun z => Quotient.mk _ z

theorem n3CircleQuotientMap_identifies_a (t : Set.Icc (0 : ℝ) 1) :
    n3CircleQuotientMap (circleEdgePoint 0 t) =
      n3CircleQuotientMap (circleEdgePoint 1 t) :=
  Quotient.sound (.rel _ _ (n3_rel_a t))

theorem n3CircleQuotientMap_identifies_b (t : Set.Icc (0 : ℝ) 1) :
    n3CircleQuotientMap (circleEdgePoint 2 t) =
      n3CircleQuotientMap (circleEdgePoint 3 t) :=
  Quotient.sound (.rel _ _ (n3_rel_b t))

theorem n3CircleQuotientMap_identifies_c (t : Set.Icc (0 : ℝ) 1) :
    n3CircleQuotientMap (circleEdgePoint 4 t) =
      n3CircleQuotientMap (circleEdgePoint 5 t) :=
  Quotient.sound (.rel _ _ (n3_rel_c t))

theorem torusCrosscapCircleQuotientMap_identifies_a
    (t : Set.Icc (0 : ℝ) 1) :
    torusCrosscapCircleQuotientMap (circleEdgePoint 0 t) =
      torusCrosscapCircleQuotientMap (circleEdgePoint 2 (reverse t)) :=
  Quotient.sound (.rel _ _ (torusCrosscap_rel_a t))

theorem torusCrosscapCircleQuotientMap_identifies_b
    (t : Set.Icc (0 : ℝ) 1) :
    torusCrosscapCircleQuotientMap (circleEdgePoint 1 t) =
      torusCrosscapCircleQuotientMap (circleEdgePoint 3 (reverse t)) :=
  Quotient.sound (.rel _ _ (torusCrosscap_rel_b t))

theorem torusCrosscapCircleQuotientMap_identifies_c
    (t : Set.Icc (0 : ℝ) 1) :
    torusCrosscapCircleQuotientMap (circleEdgePoint 4 t) =
      torusCrosscapCircleQuotientMap (circleEdgePoint 5 t) :=
  Quotient.sound (.rel _ _ (torusCrosscap_rel_c t))

end ConstructionTargets.PolygonBoundaryCircleRelations
