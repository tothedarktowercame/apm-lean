import ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence
import ConstructionTargets.CoefficientCokernelComparison

noncomputable section
namespace ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare

open CategoryTheory CategoryTheory.Limits Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.BooleanTwoCoverScaffold
open ConstructionTargets.CoefficientSubspaceUnionRangeInclusion
open ConstructionTargets.CoefficientSubspaceUnionRestrictedRangeIso
open ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility
open ConstructionTargets.CoefficientSubspaceUnionRestrictedAmbientRange
open ConstructionTargets.CoefficientSubspaceUnionRangeHomologyEquivalence

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev unionGeneratedChains (A B : Set X) :=
  (CoefficientSubspaceUnionRangeInclusion.chains R).obj
    ((ambientSubspaceRange A ⊔ ambientSubspaceRange B :
    (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet)

noncomputable def unionGeneratedAmbientInclusion (A B : Set X) :
    unionGeneratedChains R A B ⟶ CoefficientH0.SingularChains R (TopCat.of X) :=
  (CoefficientSubspaceUnionRangeInclusion.chains R).map
    (ambientSubspaceRange A ⊔ ambientSubspaceRange B).ι

noncomputable def unionGeneratedToProduction (A B : Set X) :
    unionGeneratedChains R A B ⟶
      CoefficientH0.SingularChains R (TopCat.of (A ∪ B : Set X)) :=
  unionRangeChainsInclusion R A B ≫
    (ambientSubspaceRangeChainsIso R (A ∪ B)).hom

theorem unionGenerated_relative_square (A B : Set X) :
    unionGeneratedAmbientInclusion R A B ≫ 𝟙 _ =
      unionGeneratedToProduction R A B ≫
        CoefficientRelativeSmall.subspaceMap R (A ∪ B) := by
  simp only [Category.comp_id]
  dsimp [unionGeneratedAmbientInclusion, unionGeneratedToProduction]
  rw [Category.assoc,
    ambientSubspaceRangeChainsIso_hom_comp_subspaceMap R (A ∪ B)]
  change _ = unionRangeChainsInclusion R A B ≫
    (CoefficientSubspaceUnionRangeInclusion.chains R).map
      (ambientSubspaceRange (A ∪ B)).ι
  rw [unionRangeChainsInclusion_comp_ambient]

noncomputable instance unionGeneratedAmbientInclusion_mono (A B : Set X) :
    Mono (unionGeneratedAmbientInclusion R A B) := by
  haveI : Mono (CoefficientSmallPath.coverSmallInclusion R
      (restrictedCover (A ∪ B) (booleanCover A B))) :=
    CoefficientRelativeSmall.smallInclusion_mono R _
  haveI : Mono (CoefficientRelativeSmall.subspaceMap R (A ∪ B)) :=
    CoefficientRelativeSmall.subspaceMap_mono R _
  have h : (restrictedUnionRangeChainsIso R A B).hom ≫
      unionGeneratedAmbientInclusion R A B =
    CoefficientSmallPath.coverSmallInclusion R
        (restrictedCover (A ∪ B) (booleanCover A B)) ≫
      CoefficientRelativeSmall.subspaceMap R (A ∪ B) := by
    dsimp [unionGeneratedAmbientInclusion]
    change (restrictedUnionRangeChainsIso R A B).hom ≫
      (CoefficientSubspaceUnionRangeInclusion.chains R).map
        (ambientSubspaceRange A ⊔ ambientSubspaceRange B).ι = _
    rw [restrictedUnionRangeChainsIso_hom_comp_ambient]
    dsimp [CoefficientSmallPath.coverSmallInclusion,
      CoefficientRelativeSmall.subspaceMap, restrictedUnionAmbientMap]
    change (CoefficientSubspaceUnionRangeInclusion.chains R).map _ =
      (CoefficientSubspaceUnionRangeInclusion.chains R).map _ ≫
        (CoefficientSubspaceUnionRangeInclusion.chains R).map _
    rw [← Functor.map_comp]
  haveI : Mono ((restrictedUnionRangeChainsIso R A B).hom ≫
      unionGeneratedAmbientInclusion R A B) := h ▸ inferInstance
  constructor
  intro Z g k w
  have q : g ≫ (restrictedUnionRangeChainsIso R A B).inv =
      k ≫ (restrictedUnionRangeChainsIso R A B).inv := by
    apply (cancel_mono ((restrictedUnionRangeChainsIso R A B).hom ≫
      unionGeneratedAmbientInclusion R A B)).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using w
  simpa using congrArg
    (fun u => u ≫ (restrictedUnionRangeChainsIso R A B).hom) q

theorem unionGeneratedToProduction_homologyMap_isIso (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (unionGeneratedToProduction R A B) n) := by
  haveI := unionRange_homologyMap_isIso R A B hA hB n
  dsimp [unionGeneratedToProduction]
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

noncomputable def relativeComparisonIso (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (cokernel (unionGeneratedAmbientInclusion R A B)).homology n ≅
      (CoefficientRelativeSmall.relativeChains R (A ∪ B)).homology n :=
  CoefficientCokernelComparison.comparisonIso R
    (unionGeneratedAmbientInclusion R A B)
    (CoefficientRelativeSmall.subspaceMap R (A ∪ B))
    (unionGeneratedToProduction R A B) (𝟙 _)
    (unionGenerated_relative_square R A B)
    (fun j => unionGeneratedToProduction_homologyMap_isIso R A B hA hB j)
    (fun j => by
      rw [HomologicalComplex.homologyMap_id]
      infer_instance) n

theorem relativeComparisonIso_hom (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (relativeComparisonIso R A B hA hB n).hom =
      HomologicalComplex.homologyMap
        (cokernel.map (unionGeneratedAmbientInclusion R A B)
          (CoefficientRelativeSmall.subspaceMap R (A ∪ B))
          (unionGeneratedToProduction R A B) (𝟙 _)
          (unionGenerated_relative_square R A B)) n := rfl

#print axioms unionGenerated_relative_square
#print axioms unionGeneratedAmbientInclusion_mono
#print axioms unionGeneratedToProduction_homologyMap_isIso
#print axioms relativeComparisonIso
#print axioms relativeComparisonIso_hom
end ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare
