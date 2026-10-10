import ConstructionTargets.KleinSquareEdgeOrientation

namespace KleinSquareBoundaryRelation

open Set Relation
open KleinPlaneActionSquareOrbitClassification
open KleinSquareEdgeOrientation

def SquareRel (p q : ℝ × ℝ) : Prop :=
  (∃ t : Set.Icc (0 : ℝ) 1, p = squareEdge 0 t ∧ q = squareEdge 1 t) ∨
  (∃ t : Set.Icc (0 : ℝ) 1, p = squareEdge 2 t ∧ q = squareEdge 3 t)

theorem squareRel_cases {p q : ℝ × ℝ} (h : SquareRel p q) : Cases p q := by
  rcases h with ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  · exact cases_edge_zero_one t
  · exact cases_edge_two_three t

theorem squareRel_eqvGen {p q : ℝ × ℝ} (h : SquareRel p q) :
    EqvGen SquareRel p q :=
  EqvGen.rel _ _ h

theorem squareRel_eqvGen_reverse {p q : ℝ × ℝ} (h : SquareRel p q) :
    EqvGen SquareRel q p :=
  (EqvGen.rel _ _ h).symm

#print axioms squareRel_cases
#print axioms squareRel_eqvGen
#print axioms squareRel_eqvGen_reverse

end KleinSquareBoundaryRelation
