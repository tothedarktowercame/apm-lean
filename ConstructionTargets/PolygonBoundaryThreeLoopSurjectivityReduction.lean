import ConstructionTargets.PolygonBoundaryThreeLoopContinuity

noncomputable section

namespace ConstructionTargets.PolygonBoundaryThreeLoopSurjectivityReduction

open PointWedgeQuotient
open PolygonBoundaryCircleRelations
open PolygonBoundaryThreeLoopMaps
open PolygonBoundaryInducedQuotient
open PolygonBoundaryVertexClasses
open ThreeEndpointLoopsHomeomorph
open IntervalEndpointQuotientCircle
open PolygonTorusCrosscapRelation
open Surfaces

def firstLoopPoint (t : Interval) : ThreeEndpointLoops :=
  quotientMap twoEndpointLoopsPoint endpointBase
    (.inl (quotientMap endpointBase endpointBase (.inl (intervalQuotientMap t))))

def secondLoopPoint (t : Interval) : ThreeEndpointLoops :=
  quotientMap twoEndpointLoopsPoint endpointBase
    (.inl (quotientMap endpointBase endpointBase (.inr (intervalQuotientMap t))))

def thirdLoopPoint (t : Interval) : ThreeEndpointLoops :=
  quotientMap twoEndpointLoopsPoint endpointBase (.inr (intervalQuotientMap t))

def fromUnitIcc (t : Set.Icc (0 : ℝ) 1) : Interval :=
  ⟨t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

@[simp] theorem toUnitIcc_fromUnitIcc (t : Set.Icc (0 : ℝ) 1) :
    toUnitIcc (fromUnitIcc t) = t := by
  ext
  rfl

theorem n3_edge_mem_range (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    n3CircleQuotientMap (circleEdgePoint j t) ∈ Set.range n3ThreeLoops := by
  fin_cases j
  · exact ⟨firstLoopPoint (fromUnitIcc t), by simp [firstLoopPoint]⟩
  · exact ⟨firstLoopPoint (fromUnitIcc t), by
      simp [firstLoopPoint, n3CircleQuotientMap_identifies_a]⟩
  · exact ⟨secondLoopPoint (fromUnitIcc t), by simp [secondLoopPoint]⟩
  · exact ⟨secondLoopPoint (fromUnitIcc t), by
      simp [secondLoopPoint, n3CircleQuotientMap_identifies_b]⟩
  · exact ⟨thirdLoopPoint (fromUnitIcc t), by simp [thirdLoopPoint]⟩
  · exact ⟨thirdLoopPoint (fromUnitIcc t), by
      simp [thirdLoopPoint, n3CircleQuotientMap_identifies_c]⟩

theorem torusCrosscap_edge_mem_range (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    torusCrosscapCircleQuotientMap (circleEdgePoint j t) ∈
      Set.range torusCrosscapThreeLoops := by
  fin_cases j
  · exact ⟨firstLoopPoint (fromUnitIcc t), by simp [firstLoopPoint]⟩
  · exact ⟨secondLoopPoint (fromUnitIcc t), by simp [secondLoopPoint]⟩
  · exact ⟨firstLoopPoint (fromUnitIcc (reverse t)), by
      simp [firstLoopPoint, torusCrosscapCircleQuotientMap_identifies_a]⟩
  · exact ⟨secondLoopPoint (fromUnitIcc (reverse t)), by
      simp [secondLoopPoint, torusCrosscapCircleQuotientMap_identifies_b]⟩
  · exact ⟨thirdLoopPoint (fromUnitIcc t), by simp [thirdLoopPoint]⟩
  · exact ⟨thirdLoopPoint (fromUnitIcc t), by
      simp [thirdLoopPoint, torusCrosscapCircleQuotientMap_identifies_c]⟩

theorem surjective_n3ThreeLoops_of_edge_cover
    (hcover : ∀ z : Circle, ∃ (j : Fin 6) (t : Set.Icc (0 : ℝ) 1),
      circleEdgePoint j t = z) : Function.Surjective n3ThreeLoops := by
  rintro ⟨z⟩
  obtain ⟨j, t, rfl⟩ := hcover z
  exact n3_edge_mem_range j t

theorem surjective_torusCrosscapThreeLoops_of_edge_cover
    (hcover : ∀ z : Circle, ∃ (j : Fin 6) (t : Set.Icc (0 : ℝ) 1),
      circleEdgePoint j t = z) : Function.Surjective torusCrosscapThreeLoops := by
  rintro ⟨z⟩
  obtain ⟨j, t, rfl⟩ := hcover z
  exact torusCrosscap_edge_mem_range j t

end ConstructionTargets.PolygonBoundaryThreeLoopSurjectivityReduction
