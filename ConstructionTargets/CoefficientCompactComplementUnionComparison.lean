import ConstructionTargets.CoefficientPieceRangeBiproductComparison
import ConstructionTargets.CoefficientCompactComplementSmallComparison

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementUnionComparison

open CategoryTheory Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientCompactComplementCoverSequence
open ConstructionTargets.CoefficientCompactComplementSmallComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X] [T2Space X]
variable (K L : Set X) (hK : IsCompact K) (hL : IsCompact L)

abbrev chains := (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
  (ModuleCat.of R R)

omit [T2Space X] in theorem union_eq_coverSmall :
    leftRange K L ⊔ rightRange K L = coverSmallSSet (cover K L) := by
  rw [coverSmallSSet, iSup_bool_eq]
  change leftRange K L ⊔ rightRange K L = rightRange K L ⊔ leftRange K L
  exact sup_comm _ _

noncomputable def unionChainsIso :
    (chains R).obj ((leftRange K L ⊔ rightRange K L :
      (ambientSSet K L).Subcomplex) : SSet) ≅
      CoefficientSmallPath.coverSmallChains R (cover K L) :=
  (chains R).mapIso (eqToIso (congrArg (fun P : (ambientSSet K L).Subcomplex => (P : SSet))
    (union_eq_coverSmall K L)))

noncomputable def unionHomologyIso (n : ℕ) :
    ((chains R).obj ((leftRange K L ⊔ rightRange K L :
      (ambientSSet K L).Subcomplex) : SSet)).homology n ≅
      (CoefficientH0.SingularChains R (TopCat.of (ambient K L))).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (unionChainsIso R K L) ≪≫ ambientHomologyIso R K L hK hL n

theorem unionHomologyIso_hom (n : ℕ) :
    (unionHomologyIso R K L hK hL n).hom =
      HomologicalComplex.homologyMap (unionChainsIso R K L).hom n ≫
        (ambientHomologyIso R K L hK hL n).hom := rfl

theorem unionHomologyIso_inv (n : ℕ) :
    (unionHomologyIso R K L hK hL n).inv =
      (ambientHomologyIso R K L hK hL n).inv ≫
        HomologicalComplex.homologyMap (unionChainsIso R K L).inv n := rfl

#print axioms union_eq_coverSmall
#print axioms unionChainsIso
#print axioms unionHomologyIso
#print axioms unionHomologyIso_hom
#print axioms unionHomologyIso_inv
end ConstructionTargets.CoefficientCompactComplementUnionComparison
