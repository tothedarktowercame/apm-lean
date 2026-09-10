import ConstructionTargets.CoefficientSubspaceUnionRestrictedAmbientRange
import ConstructionTargets.CoefficientSubspaceUnionCoverSmallComparison

noncomputable section
namespace ConstructionTargets.CoefficientSubspaceUnionRestrictedRangeIso

open CategoryTheory Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.BooleanTwoCoverScaffold
open ConstructionTargets.CoefficientSubspaceUnionRangeInclusion
open ConstructionTargets.CoefficientSubspaceUnionRestrictedAmbientRange

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

noncomputable instance restrictedUnionAmbientMap_mono (A B : Set X) :
    Mono (restrictedUnionAmbientMap A B) := by
  dsimp [restrictedUnionAmbientMap]
  infer_instance

noncomputable def restrictedUnionRangeSSetIso (A B : Set X) :
    (coverSmallSSet (restrictedCover (A ∪ B) (booleanCover A B)) : SSet) ≅
      ((ambientSubspaceRange A ⊔ ambientSubspaceRange B :
        (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) :=
  asIso (Subfunctor.toRange (restrictedUnionAmbientMap A B)) ≪≫
    eqToIso (congrArg
      (fun P : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex => (P : SSet))
      (restrictedUnionAmbientMap_range A B))

noncomputable def restrictedUnionRangeChainsIso (A B : Set X) :
    CoefficientSmallPath.coverSmallChains R
        (restrictedCover (A ∪ B) (booleanCover A B)) ≅
      (chains R).obj ((ambientSubspaceRange A ⊔ ambientSubspaceRange B :
        (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) :=
  (chains R).mapIso (restrictedUnionRangeSSetIso A B)

theorem restrictedUnionRangeSSetIso_hom_comp_ambient (A B : Set X) :
    (restrictedUnionRangeSSetIso A B).hom ≫
        (ambientSubspaceRange A ⊔ ambientSubspaceRange B).ι =
      restrictedUnionAmbientMap A B := by
  dsimp [restrictedUnionRangeSSetIso]
  simp only [Category.assoc]
  calc
    _ = Subfunctor.toRange (restrictedUnionAmbientMap A B) ≫
        (SSet.Subcomplex.range (restrictedUnionAmbientMap A B)).ι := by
      apply congrArg (fun k => Subfunctor.toRange
        (restrictedUnionAmbientMap A B) ≫ k)
      exact eqToIso_subcomplex_hom_comp_ι _ _
        (restrictedUnionAmbientMap_range A B)
    _ = restrictedUnionAmbientMap A B :=
      Subfunctor.toRange_ι (restrictedUnionAmbientMap A B)

theorem restrictedUnionRangeChainsIso_hom_comp_ambient (A B : Set X) :
    (restrictedUnionRangeChainsIso R A B).hom ≫
        (chains R).map (ambientSubspaceRange A ⊔ ambientSubspaceRange B).ι =
      (chains R).map (restrictedUnionAmbientMap A B) := by
  change (chains R).map (restrictedUnionRangeSSetIso A B).hom ≫ _ = _
  rw [← Functor.map_comp, restrictedUnionRangeSSetIso_hom_comp_ambient]

#print axioms restrictedUnionRangeSSetIso
#print axioms restrictedUnionRangeChainsIso
#print axioms restrictedUnionRangeSSetIso_hom_comp_ambient
#print axioms restrictedUnionRangeChainsIso_hom_comp_ambient
end ConstructionTargets.CoefficientSubspaceUnionRestrictedRangeIso
