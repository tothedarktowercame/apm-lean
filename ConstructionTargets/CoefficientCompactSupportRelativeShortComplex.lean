import ConstructionTargets.CoefficientCompactSupportRelativeArrowComplex

noncomputable section
namespace ConstructionTargets.CoefficientCompactSupportRelativeShortComplex

open CategoryTheory CategoryTheory.Limits Set
open ConstructionTargets.CoefficientCompactSupportRestrictionMaps
open ConstructionTargets.CoefficientCompactSupportPiecesToIntersection
open ConstructionTargets.CoefficientCompactSupportRelativeArrowComplex

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

noncomputable def shortComplex (K L : Set X) :
    ShortComplex (HomologicalComplex (ModuleCat R) (ComplexShape.down ℕ)) :=
  ShortComplex.mk (restrictPiecesChain R K L) (piecesToIntersection R K L)
    (relative_arrows_zero R K L)

theorem shortComplex_f (K L : Set X) :
    (shortComplex R K L).f = restrictPiecesChain R K L := rfl

theorem shortComplex_g (K L : Set X) :
    (shortComplex R K L).g = piecesToIntersection R K L := rfl

theorem shortComplex_zero (K L : Set X) :
    (shortComplex R K L).f ≫ (shortComplex R K L).g = 0 :=
  (shortComplex R K L).zero

#print axioms shortComplex
#print axioms shortComplex_f
#print axioms shortComplex_g
#print axioms shortComplex_zero
end ConstructionTargets.CoefficientCompactSupportRelativeShortComplex
