import ConstructionTargets.CoefficientIntersectionRangeNaturality

noncomputable section
namespace ConstructionTargets.CoefficientPieceRangeBiproductComparison

open CategoryTheory CategoryTheory.Limits Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.CoefficientAmbientSubspaceRangeComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev chains := (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
  (ModuleCat.of R R)

noncomputable def pieceHomologyIso (A B : Set X) (n : ℕ) :
    ((chains R).obj (ambientSubspaceRange A : SSet)).homology n ⊞
        ((chains R).obj (ambientSubspaceRange B : SSet)).homology n ≅
      ((chains R).obj (TopCat.toSSet.obj (TopCat.of A))).homology n ⊞
        ((chains R).obj (TopCat.toSSet.obj (TopCat.of B))).homology n :=
  biprod.mapIso (rangeHomologyIso R A n) (rangeHomologyIso R B n)

theorem pieceHomologyIso_hom_fst (A B : Set X) (n : ℕ) :
    (pieceHomologyIso R A B n).hom ≫ biprod.fst =
      biprod.fst ≫ (rangeHomologyIso R A n).hom := by
  exact biprod.map_fst _ _

theorem pieceHomologyIso_hom_snd (A B : Set X) (n : ℕ) :
    (pieceHomologyIso R A B n).hom ≫ biprod.snd =
      biprod.snd ≫ (rangeHomologyIso R B n).hom := by
  exact biprod.map_snd _ _

theorem pieceHomologyIso_inv_fst (A B : Set X) (n : ℕ) :
    (pieceHomologyIso R A B n).inv ≫ biprod.fst =
      biprod.fst ≫ (rangeHomologyIso R A n).inv := by
  exact biprod.map_fst _ _

theorem pieceHomologyIso_inv_snd (A B : Set X) (n : ℕ) :
    (pieceHomologyIso R A B n).inv ≫ biprod.snd =
      biprod.snd ≫ (rangeHomologyIso R B n).inv := by
  exact biprod.map_snd _ _

#print axioms pieceHomologyIso
#print axioms pieceHomologyIso_hom_fst
#print axioms pieceHomologyIso_hom_snd
#print axioms pieceHomologyIso_inv_fst
#print axioms pieceHomologyIso_inv_snd
end ConstructionTargets.CoefficientPieceRangeBiproductComparison
