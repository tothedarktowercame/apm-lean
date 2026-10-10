import ConstructionTargets.KleinDiskSquareCarrier

namespace KleinSquareEdgeOrientation

open Set
open ConstructionTargets.Surfaces
open KleinPlaneActionSquareOrbitClassification

def squareEdge (edge : Fin 4) (t : Set.Icc (0 : ℝ) 1) : ℝ × ℝ :=
  match edge.1 with
  | 0 => (0, t.1)
  | 1 => (1, t.1)
  | 2 => (t.1, 0)
  | _ => (1 - t.1, 1)

theorem squareEdge_zero (t : Set.Icc (0 : ℝ) 1) :
    squareEdge 0 t = (0, t.1) := rfl

theorem squareEdge_one (t : Set.Icc (0 : ℝ) 1) :
    squareEdge 1 t = (1, t.1) := rfl

theorem squareEdge_two (t : Set.Icc (0 : ℝ) 1) :
    squareEdge 2 t = (t.1, 0) := rfl

theorem squareEdge_three (t : Set.Icc (0 : ℝ) 1) :
    squareEdge 3 t = (1 - t.1, 1) := rfl

theorem inSquare_squareEdge (edge : Fin 4) (t : Set.Icc (0 : ℝ) 1) :
    InSquare (squareEdge edge t) := by
  rcases t.2 with ⟨ht0, ht1⟩
  fin_cases edge <;> simp [InSquare, squareEdge, ht0, ht1] <;> linarith

theorem cases_edge_zero_one (t : Set.Icc (0 : ℝ) 1) :
    Cases (squareEdge 0 t) (squareEdge 1 t) := by
  right
  left
  exact ⟨1, rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩

theorem cases_edge_two_three (t : Set.Icc (0 : ℝ) 1) :
    Cases (squareEdge 2 t) (squareEdge 3 t) := by
  right
  right
  exact ⟨1, rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

theorem surfaceRel_edge_zero_one (t : Set.Icc (0 : ℝ) 1) :
    SurfaceRel false 2 (edgePoint 4 0 t) (edgePoint 4 1 t) := by
  exact ⟨0, by omega, t, rfl, rfl⟩

theorem surfaceRel_edge_two_three (t : Set.Icc (0 : ℝ) 1) :
    SurfaceRel false 2 (edgePoint 4 2 t) (edgePoint 4 3 t) := by
  exact ⟨1, by omega, t, by norm_num, by norm_num⟩

#print axioms cases_edge_zero_one
#print axioms cases_edge_two_three
#print axioms surfaceRel_edge_zero_one
#print axioms surfaceRel_edge_two_three

end KleinSquareEdgeOrientation
