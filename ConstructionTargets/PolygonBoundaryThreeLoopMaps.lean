import ConstructionTargets.ThreeEndpointLoopsHomeomorph

noncomputable section

namespace ConstructionTargets.PolygonBoundaryThreeLoopMaps

open PointWedgeQuotient
open PolygonBoundaryCircleRelations
open PolygonBoundaryVertexClasses
open PolygonBoundaryInducedQuotient
open IntervalEndpointQuotientCircle
open ThreeEndpointLoopsHomeomorph
open Surfaces
open PolygonTorusCrosscapRelation

def toUnitIcc (t : Interval) : Set.Icc (0 : ℝ) 1 :=
  ⟨t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

private theorem wedgeLift_respects {X Y Z : Type*} {x₀ : X} {y₀ : Y}
    (f : X → Z) (g : Y → Z) (hbase : f x₀ = g y₀)
    (a b : Sum X Y) (hab : Relation.EqvGen (Rel x₀ y₀) a b) :
    Sum.elim f g a = Sum.elim f g b := by
  induction hab with
  | rel a b hab => cases hab; exact hbase
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def wedgeLift {X Y Z : Type*} {x₀ : X} {y₀ : Y}
    (f : X → Z) (g : Y → Z) (hbase : f x₀ = g y₀) :
    Wedge x₀ y₀ → Z :=
  Quotient.lift (Sum.elim f g) (wedgeLift_respects f g hbase)

@[simp] theorem wedgeLift_left {X Y Z : Type*} {x₀ : X} {y₀ : Y}
    (f : X → Z) (g : Y → Z) (hbase : f x₀ = g y₀) (x : X) :
    wedgeLift f g hbase (quotientMap x₀ y₀ (.inl x)) = f x := rfl

@[simp] theorem wedgeLift_right {X Y Z : Type*} {x₀ : X} {y₀ : Y}
    (f : X → Z) (g : Y → Z) (hbase : f x₀ = g y₀) (y : Y) :
    wedgeLift f g hbase (quotientMap x₀ y₀ (.inr y)) = g y := rfl

private theorem n3_edge0_endpoints :
    n3CircleQuotientMap (circleEdgePoint 0 zeroIcc) =
      n3CircleQuotientMap (circleEdgePoint 0 oneIcc) := by
  exact n3_vertex_0_eq_1.trans (congrArg n3CircleQuotientMap
    (circleEdgePoint_one_eq_succ_zero 0 (by norm_num))).symm

private theorem n3_edge2_endpoints :
    n3CircleQuotientMap (circleEdgePoint 2 zeroIcc) =
      n3CircleQuotientMap (circleEdgePoint 2 oneIcc) := by
  exact n3_vertex_2_eq_3.trans (congrArg n3CircleQuotientMap
    (circleEdgePoint_one_eq_succ_zero 2 (by norm_num))).symm

private theorem n3_edge4_endpoints :
    n3CircleQuotientMap (circleEdgePoint 4 zeroIcc) =
      n3CircleQuotientMap (circleEdgePoint 4 oneIcc) := by
  exact n3_vertex_4_eq_5.trans (congrArg n3CircleQuotientMap
    (circleEdgePoint_one_eq_succ_zero 4 (by norm_num))).symm

def n3Loop (j : Fin 6)
    (hend : n3CircleQuotientMap (circleEdgePoint j zeroIcc) =
      n3CircleQuotientMap (circleEdgePoint j oneIcc)) :
    EndpointQuotient → CircleQuotient (SurfaceRel false 3) :=
  Quot.lift (fun t => n3CircleQuotientMap (circleEdgePoint j (toUnitIcc t))) (by
    intro a b h
    cases h
    simpa [toUnitIcc, zeroIcc, oneIcc] using hend)

def n3LoopA := n3Loop 0 n3_edge0_endpoints
def n3LoopB := n3Loop 2 n3_edge2_endpoints
def n3LoopC := n3Loop 4 n3_edge4_endpoints

@[simp] theorem n3LoopA_mk (t : Interval) :
    n3LoopA (intervalQuotientMap t) =
      n3CircleQuotientMap (circleEdgePoint 0 (toUnitIcc t)) := rfl
@[simp] theorem n3LoopB_mk (t : Interval) :
    n3LoopB (intervalQuotientMap t) =
      n3CircleQuotientMap (circleEdgePoint 2 (toUnitIcc t)) := rfl
@[simp] theorem n3LoopC_mk (t : Interval) :
    n3LoopC (intervalQuotientMap t) =
      n3CircleQuotientMap (circleEdgePoint 4 (toUnitIcc t)) := rfl

private theorem n3_base_ab : n3LoopA endpointBase = n3LoopB endpointBase := by
  simpa [n3LoopA, n3LoopB, n3Loop, endpointBase, toUnitIcc, vertex] using
    (n3_all_vertices 2).symm

def n3TwoLoops : TwoEndpointLoops → CircleQuotient (SurfaceRel false 3) :=
  wedgeLift n3LoopA n3LoopB n3_base_ab

private theorem n3_base_abc : n3TwoLoops twoEndpointLoopsPoint = n3LoopC endpointBase := by
  simpa [n3TwoLoops, twoEndpointLoopsPoint, n3LoopA, n3LoopC, n3Loop,
    endpointBase, toUnitIcc, vertex] using (n3_all_vertices 4).symm

def n3ThreeLoops : ThreeEndpointLoops → CircleQuotient (SurfaceRel false 3) :=
  wedgeLift n3TwoLoops n3LoopC n3_base_abc

@[simp] theorem n3ThreeLoops_first (x : EndpointQuotient) :
    n3ThreeLoops (quotientMap twoEndpointLoopsPoint endpointBase
      (.inl (quotientMap endpointBase endpointBase (.inl x)))) = n3LoopA x := rfl

@[simp] theorem n3ThreeLoops_second (x : EndpointQuotient) :
    n3ThreeLoops (quotientMap twoEndpointLoopsPoint endpointBase
      (.inl (quotientMap endpointBase endpointBase (.inr x)))) = n3LoopB x := rfl

@[simp] theorem n3ThreeLoops_third (x : EndpointQuotient) :
    n3ThreeLoops (quotientMap twoEndpointLoopsPoint endpointBase (.inr x)) =
      n3LoopC x := rfl

private theorem tc_edge0_endpoints :
    torusCrosscapCircleQuotientMap (circleEdgePoint 0 zeroIcc) =
      torusCrosscapCircleQuotientMap (circleEdgePoint 0 oneIcc) := by
  exact (torusCrosscap_all_vertices 0).trans
    ((torusCrosscap_all_vertices 1).symm.trans (congrArg
      torusCrosscapCircleQuotientMap
      (circleEdgePoint_one_eq_succ_zero 0 (by norm_num))).symm)

private theorem tc_edge1_endpoints :
    torusCrosscapCircleQuotientMap (circleEdgePoint 1 zeroIcc) =
      torusCrosscapCircleQuotientMap (circleEdgePoint 1 oneIcc) := by
  exact (torusCrosscap_all_vertices 1).trans
    ((torusCrosscap_all_vertices 2).symm.trans (congrArg
      torusCrosscapCircleQuotientMap
      (circleEdgePoint_one_eq_succ_zero 1 (by norm_num))).symm)

private theorem tc_edge4_endpoints :
    torusCrosscapCircleQuotientMap (circleEdgePoint 4 zeroIcc) =
      torusCrosscapCircleQuotientMap (circleEdgePoint 4 oneIcc) := by
  exact (torusCrosscap_all_vertices 4).trans
    ((torusCrosscap_all_vertices 5).symm.trans (congrArg
      torusCrosscapCircleQuotientMap
      (circleEdgePoint_one_eq_succ_zero 4 (by norm_num))).symm)

def torusCrosscapLoop (j : Fin 6)
    (hend : torusCrosscapCircleQuotientMap (circleEdgePoint j zeroIcc) =
      torusCrosscapCircleQuotientMap (circleEdgePoint j oneIcc)) :
    EndpointQuotient → CircleQuotient TorusCrosscapRel :=
  Quot.lift (fun t => torusCrosscapCircleQuotientMap
    (circleEdgePoint j (toUnitIcc t))) (by
    intro a b h
    cases h
    simpa [toUnitIcc, zeroIcc, oneIcc] using hend)

def torusCrosscapLoopA := torusCrosscapLoop 0 tc_edge0_endpoints
def torusCrosscapLoopB := torusCrosscapLoop 1 tc_edge1_endpoints
def torusCrosscapLoopC := torusCrosscapLoop 4 tc_edge4_endpoints

@[simp] theorem torusCrosscapLoopA_mk (t : Interval) :
    torusCrosscapLoopA (intervalQuotientMap t) =
      torusCrosscapCircleQuotientMap (circleEdgePoint 0 (toUnitIcc t)) := rfl
@[simp] theorem torusCrosscapLoopB_mk (t : Interval) :
    torusCrosscapLoopB (intervalQuotientMap t) =
      torusCrosscapCircleQuotientMap (circleEdgePoint 1 (toUnitIcc t)) := rfl
@[simp] theorem torusCrosscapLoopC_mk (t : Interval) :
    torusCrosscapLoopC (intervalQuotientMap t) =
      torusCrosscapCircleQuotientMap (circleEdgePoint 4 (toUnitIcc t)) := rfl

private theorem tc_base_ab :
    torusCrosscapLoopA endpointBase = torusCrosscapLoopB endpointBase := by
  simpa [torusCrosscapLoopA, torusCrosscapLoopB, torusCrosscapLoop,
    endpointBase, toUnitIcc, vertex] using (torusCrosscap_all_vertices 1).symm

def torusCrosscapTwoLoops : TwoEndpointLoops → CircleQuotient TorusCrosscapRel :=
  wedgeLift torusCrosscapLoopA torusCrosscapLoopB tc_base_ab

private theorem tc_base_abc :
    torusCrosscapTwoLoops twoEndpointLoopsPoint = torusCrosscapLoopC endpointBase := by
  simpa [torusCrosscapTwoLoops, twoEndpointLoopsPoint, torusCrosscapLoopA,
    torusCrosscapLoopC, torusCrosscapLoop, endpointBase, toUnitIcc, vertex] using
    (torusCrosscap_all_vertices 4).symm

def torusCrosscapThreeLoops : ThreeEndpointLoops → CircleQuotient TorusCrosscapRel :=
  wedgeLift torusCrosscapTwoLoops torusCrosscapLoopC tc_base_abc

@[simp] theorem torusCrosscapThreeLoops_first (x : EndpointQuotient) :
    torusCrosscapThreeLoops (quotientMap twoEndpointLoopsPoint endpointBase
      (.inl (quotientMap endpointBase endpointBase (.inl x)))) =
      torusCrosscapLoopA x := rfl

@[simp] theorem torusCrosscapThreeLoops_second (x : EndpointQuotient) :
    torusCrosscapThreeLoops (quotientMap twoEndpointLoopsPoint endpointBase
      (.inl (quotientMap endpointBase endpointBase (.inr x)))) =
      torusCrosscapLoopB x := rfl

@[simp] theorem torusCrosscapThreeLoops_third (x : EndpointQuotient) :
    torusCrosscapThreeLoops
      (quotientMap twoEndpointLoopsPoint endpointBase (.inr x)) =
      torusCrosscapLoopC x := rfl

end ConstructionTargets.PolygonBoundaryThreeLoopMaps
