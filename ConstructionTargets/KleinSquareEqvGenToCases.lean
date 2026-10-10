import ConstructionTargets.KleinSquareCasesToEqvGen

namespace KleinSquareEqvGenToCases

open Set Relation
open KleinPlaneAffineAction
open KleinPlaneActionSquareOrbitClassification
open KleinSquareEdgeOrientation
open KleinSquareBoundaryRelation

def SameOrbit (p q : ℝ × ℝ) : Prop :=
  ∃ g : KleinPresentedGroupCoordinateModel.PresentedKleinGroup, g • p = q

theorem sameOrbit_refl (p : ℝ × ℝ) : SameOrbit p p := by
  exact ⟨1, one_smul _ _⟩

theorem sameOrbit_symm {p q : ℝ × ℝ} (h : SameOrbit p q) : SameOrbit q p := by
  rcases h with ⟨g, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  rw [← mul_smul]
  simp

theorem sameOrbit_trans {p q r : ℝ × ℝ} (hpq : SameOrbit p q) (hqr : SameOrbit q r) :
    SameOrbit p r := by
  rcases hpq with ⟨g, rfl⟩
  rcases hqr with ⟨k, rfl⟩
  exact ⟨k * g, mul_smul _ _ _⟩

theorem squareRel_sameOrbit {p q : ℝ × ℝ} (h : SquareRel p q) : SameOrbit p q := by
  rcases h with ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  · exact (sameOrbit_iff_cases (inSquare_squareEdge 0 t) (inSquare_squareEdge 1 t)).2
      (cases_edge_zero_one t)
  · exact (sameOrbit_iff_cases (inSquare_squareEdge 2 t) (inSquare_squareEdge 3 t)).2
      (cases_edge_two_three t)

theorem eqvGen_sameOrbit {p q : ℝ × ℝ} (h : EqvGen SquareRel p q) : SameOrbit p q := by
  induction h with
  | rel x y hxy => exact squareRel_sameOrbit hxy
  | refl x => exact sameOrbit_refl x
  | symm x y _ ih => exact sameOrbit_symm ih
  | trans x y z _ _ ihxy ihyz => exact sameOrbit_trans ihxy ihyz

theorem eqvGen_cases {p q : ℝ × ℝ} (hp : InSquare p) (hq : InSquare q)
    (h : EqvGen SquareRel p q) : Cases p q :=
  (sameOrbit_iff_cases hp hq).1 (eqvGen_sameOrbit h)

#print axioms eqvGen_cases

end KleinSquareEqvGenToCases
