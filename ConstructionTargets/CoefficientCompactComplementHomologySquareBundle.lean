import ConstructionTargets.CoefficientCompactComplementHomologySquares

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementHomologySquareBundle

open CategoryTheory Set
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientCompactComplementHomologyTransport
open ConstructionTargets.CoefficientCompactComplementHomologySquares

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev chains := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj
  (ModuleCat.of R R)

/-- The three actual complement identifications commute with their literal
inclusions into `X`, simultaneously and in the forward direction needed for
Mayer--Vietoris conjugation. -/
theorem homology_square_bundle (K L : Set X) (n : ℕ) :
    ((leftHomologyIso R K L n).hom ≫
          HomologicalComplex.homologyMap
            ((chains R).map (TopCat.ofHom (originalLeftInclusion K))) n =
        HomologicalComplex.homologyMap
          ((chains R).map (TopCat.ofHom (nestedLeftInclusion K L))) n) ∧
    ((rightHomologyIso R K L n).hom ≫
          HomologicalComplex.homologyMap
            ((chains R).map (TopCat.ofHom (originalRightInclusion L))) n =
        HomologicalComplex.homologyMap
          ((chains R).map (TopCat.ofHom (nestedRightInclusion K L))) n) ∧
    ((overlapHomologyIso R K L n).hom ≫
          HomologicalComplex.homologyMap
            ((chains R).map (TopCat.ofHom (originalOverlapInclusion K L))) n =
        HomologicalComplex.homologyMap
          ((chains R).map (TopCat.ofHom (nestedOverlapInclusion K L))) n) := by
  exact ⟨left_homology_square R K L n,
    right_homology_square R K L n,
    overlap_homology_square R K L n⟩

#print axioms homology_square_bundle
end ConstructionTargets.CoefficientCompactComplementHomologySquareBundle
