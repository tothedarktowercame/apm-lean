import ConstructionTargets.RelationQuotientLeftInverse

noncomputable section

namespace ConstructionTargets.PolygonBoundaryGeneratorNormalForms

open Surfaces
open PolygonTorusCrosscapRelation
open PolygonBoundaryCircleRelations
open PolygonBoundaryInducedQuotient
open PolygonBoundaryCircleSource

private theorem circle_eq_edge_of_boundary_val_eq (z : Circle) (j : Fin 6)
    (t : Set.Icc (0 : ℝ) 1)
    (h : (circleToBoundary z).1 = edgePoint 6 j t) :
    z = circleEdgePoint j t := by
  rw [← boundaryToCircle_circleToBoundary z]
  apply congrArg boundaryToCircle
  apply Subtype.ext
  exact h

theorem torusCrosscapRel_iff {x y : Disk} : TorusCrosscapRel x y ↔
    (∃ t, x = edgePoint 6 0 t ∧ y = edgePoint 6 2 (reverse t)) ∨
    (∃ t, x = edgePoint 6 1 t ∧ y = edgePoint 6 3 (reverse t)) ∨
    (∃ t, x = edgePoint 6 4 t ∧ y = edgePoint 6 5 t) := by
  constructor
  · intro h; cases h with
    | a t => exact Or.inl ⟨t, rfl, rfl⟩
    | b t => exact Or.inr (Or.inl ⟨t, rfl, rfl⟩)
    | c t => exact Or.inr (Or.inr ⟨t, rfl, rfl⟩)
  · rintro (⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩)
    · exact .a t
    · exact .b t
    · exact .c t

theorem n3CircleRel_iff (z w : Circle) :
    N3CircleRel z w ↔
      (∃ t : Set.Icc (0 : ℝ) 1,
        z = circleEdgePoint 0 t ∧ w = circleEdgePoint 1 t) ∨
      (∃ t : Set.Icc (0 : ℝ) 1,
        z = circleEdgePoint 2 t ∧ w = circleEdgePoint 3 t) ∨
      (∃ t : Set.Icc (0 : ℝ) 1,
        z = circleEdgePoint 4 t ∧ w = circleEdgePoint 5 t) := by
  change SurfaceRel false 3 (circleToBoundary z).1 (circleToBoundary w).1 ↔ _
  constructor
  · rintro ⟨j, hj, t, hz, hw⟩
    interval_cases j
    · left; exact ⟨t, circle_eq_edge_of_boundary_val_eq z 0 t (by simpa using hz),
        circle_eq_edge_of_boundary_val_eq w 1 t (by simpa using hw)⟩
    · right; left; exact ⟨t, circle_eq_edge_of_boundary_val_eq z 2 t (by simpa using hz),
        circle_eq_edge_of_boundary_val_eq w 3 t (by simpa using hw)⟩
    · right; right; exact ⟨t, circle_eq_edge_of_boundary_val_eq z 4 t (by simpa using hz),
        circle_eq_edge_of_boundary_val_eq w 5 t (by simpa using hw)⟩
  · rintro (⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩)
    · exact n3_rel_a t
    · exact n3_rel_b t
    · exact n3_rel_c t

theorem torusCrosscapCircleRel_iff (z w : Circle) :
    TorusCrosscapCircleRel z w ↔
      (∃ t : Set.Icc (0 : ℝ) 1,
        z = circleEdgePoint 0 t ∧ w = circleEdgePoint 2 (reverse t)) ∨
      (∃ t : Set.Icc (0 : ℝ) 1,
        z = circleEdgePoint 1 t ∧ w = circleEdgePoint 3 (reverse t)) ∨
      (∃ t : Set.Icc (0 : ℝ) 1,
        z = circleEdgePoint 4 t ∧ w = circleEdgePoint 5 t) := by
  change TorusCrosscapRel (circleToBoundary z).1 (circleToBoundary w).1 ↔ _
  constructor
  · intro h
    rcases torusCrosscapRel_iff.mp h with ⟨t, hz, hw⟩ | ⟨t, hz, hw⟩ | ⟨t, hz, hw⟩
    · left; exact ⟨t, circle_eq_edge_of_boundary_val_eq z 0 t hz,
        circle_eq_edge_of_boundary_val_eq w 2 (reverse t) hw⟩
    · right; left; exact ⟨t, circle_eq_edge_of_boundary_val_eq z 1 t hz,
        circle_eq_edge_of_boundary_val_eq w 3 (reverse t) hw⟩
    · right; right; exact ⟨t, circle_eq_edge_of_boundary_val_eq z 4 t hz,
        circle_eq_edge_of_boundary_val_eq w 5 t hw⟩
  · rintro (⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩)
    · exact torusCrosscap_rel_a t
    · exact torusCrosscap_rel_b t
    · exact torusCrosscap_rel_c t

end ConstructionTargets.PolygonBoundaryGeneratorNormalForms
