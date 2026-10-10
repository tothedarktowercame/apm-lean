import ConstructionTargets.KleinSquareEqvGenToCases

namespace KleinSquareEqvGenCasesIff

open Relation
open KleinPlaneActionSquareOrbitClassification
open KleinSquareBoundaryRelation
open KleinSquareCasesToEqvGen
open KleinSquareEqvGenToCases

theorem eqvGen_iff_cases {p q : ℝ × ℝ} (hp : InSquare p) (hq : InSquare q) :
    EqvGen SquareRel p q ↔ Cases p q := by
  constructor
  · exact eqvGen_cases hp hq
  · exact cases_eqvGen hp hq

#print axioms eqvGen_iff_cases

end KleinSquareEqvGenCasesIff
