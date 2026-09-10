import ConstructionTargets.CoefficientHomologyBiprodIso
import ConstructionTargets.CoefficientPieceRangeBiproductComparison

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementPiecesComparison

open CategoryTheory CategoryTheory.Limits Set
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientCompactComplementCoverSequence
open ConstructionTargets.CoefficientAmbientSubspaceRangeComparison
open ConstructionTargets.CoefficientPieceRangeBiproductComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

noncomputable def piecesHomologyIso (K L : Set X) (n : ℕ) :
    ((shortComplex R K L).X₂).homology n ≅
      ((CoefficientPieceRangeBiproductComparison.chains R).obj
        (TopCat.toSSet.obj (TopCat.of (left K L)))).homology n ⊞
      ((CoefficientPieceRangeBiproductComparison.chains R).obj
        (TopCat.toSSet.obj (TopCat.of (right K L)))).homology n := by
  dsimp [shortComplex, ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortComplex,
    ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortComplex,
    ConstructionTargets.SingularExcision.subcomplexMayerVietorisShortComplex]
  exact ConstructionTargets.CoefficientHomologyBiprodIso.homologyBiprodIso R
      ((CoefficientPieceRangeBiproductComparison.chains R).obj
        (leftRange K L : SSet))
      ((CoefficientPieceRangeBiproductComparison.chains R).obj
        (rightRange K L : SSet)) n ≪≫
    pieceHomologyIso R (left K L) (right K L) n

theorem piecesHomologyIso_hom (K L : Set X) (n : ℕ) :
    (piecesHomologyIso R K L n).hom =
      (ConstructionTargets.CoefficientHomologyBiprodIso.homologyBiprodIso R
        ((CoefficientPieceRangeBiproductComparison.chains R).obj (leftRange K L : SSet))
        ((CoefficientPieceRangeBiproductComparison.chains R).obj (rightRange K L : SSet)) n).hom ≫
      (pieceHomologyIso R (left K L) (right K L) n).hom := rfl

theorem piecesHomologyIso_inv (K L : Set X) (n : ℕ) :
    (piecesHomologyIso R K L n).inv =
      (pieceHomologyIso R (left K L) (right K L) n).inv ≫
      (ConstructionTargets.CoefficientHomologyBiprodIso.homologyBiprodIso R
        ((CoefficientPieceRangeBiproductComparison.chains R).obj (leftRange K L : SSet))
        ((CoefficientPieceRangeBiproductComparison.chains R).obj (rightRange K L : SSet)) n).inv := rfl

#print axioms piecesHomologyIso
#print axioms piecesHomologyIso_hom
#print axioms piecesHomologyIso_inv
end ConstructionTargets.CoefficientCompactComplementPiecesComparison
