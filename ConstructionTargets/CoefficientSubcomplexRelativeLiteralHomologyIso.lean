import ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularExcision
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
open ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison
open ConstructionTargets.CoefficientAmbientSubspaceRangeCompatibility
open ConstructionTargets.CoefficientCokernelComparison

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

noncomputable local instance literalSubspace_mono (A : Set X) :
    Mono (CoefficientRelativeSmall.subspaceMap R A) :=
  CoefficientRelativeSmall.subspaceMap_mono R A

noncomputable local instance rangeAmbient_mono (A : Set X) :
    Mono (leftAmbient R (P A)) := by
  letI h₁ : Mono (CoefficientRelativeSmall.subspaceMap R A) :=
    CoefficientRelativeSmall.subspaceMap_mono R A
  letI h₂ : Mono (ambientSubspaceRangeChainsIso R A).hom := inferInstance
  letI h₃ : Mono ((ambientSubspaceRangeChainsIso R A).hom ≫
      CoefficientRelativeSmall.subspaceMap R A) :=
    mono_comp (ambientSubspaceRangeChainsIso R A).hom
      (CoefficientRelativeSmall.subspaceMap R A)
  have h := rangeRelative_square R A
  rw [Category.comp_id] at h
  rw [h]
  exact h₃

noncomputable def rangeRelativeIso (A : Set X) (n : ℕ) :
    (cokernel (leftAmbient R (P A))).homology n ≅
      (CoefficientRelativeSmall.relativeChains R A).homology n :=
  by
  exact comparisonIso R
    (f := leftAmbient R (P A))
    (f' := CoefficientRelativeSmall.subspaceMap R A)
    (a := (ambientSubspaceRangeChainsIso R A).hom) (b := 𝟙 _)
    (rangeRelative_square R A)
    (fun j => by
      change IsIso (HomologicalComplex.homologyMap
        (ambientSubspaceRangeChainsIso R A).hom j)
      infer_instance)
    (fun j => by
      have h := HomologicalComplex.homologyMap_id
        ((CoefficientAmbientSubspaceRangeCompatibility.chains R).obj
          (TopCat.toSSet.obj (TopCat.of X))) j
      exact h.symm ▸ (IsIso.mk ⟨𝟙 _, rfl, rfl⟩)) n

noncomputable local instance intersectionAmbient_mono (A B : Set X) :
    Mono (intersectionAmbient R (P A) (P B)) := by
  letI h₁ : Mono (CoefficientRelativeSmall.subspaceMap R (A ∩ B)) :=
    CoefficientRelativeSmall.subspaceMap_mono R (A ∩ B)
  letI h₂ : Mono (intersectionRangeChainsToLiteral R A B).hom := inferInstance
  letI h₃ : Mono ((intersectionRangeChainsToLiteral R A B).hom ≫
      CoefficientRelativeSmall.subspaceMap R (A ∩ B)) :=
    mono_comp (intersectionRangeChainsToLiteral R A B).hom
      (CoefficientRelativeSmall.subspaceMap R (A ∩ B))
  have h := intersectionRelative_square R A B
  rw [Category.comp_id] at h
  rw [h]
  exact h₃

noncomputable def intersectionRelativeIso (A B : Set X) (n : ℕ) :
    (cokernel (intersectionAmbient R (P A) (P B))).homology n ≅
      (CoefficientRelativeSmall.relativeChains R (A ∩ B)).homology n :=
  by
  exact comparisonIso R
    (f := intersectionAmbient R (P A) (P B))
    (f' := CoefficientRelativeSmall.subspaceMap R (A ∩ B))
    (a := (intersectionRangeChainsToLiteral R A B).hom) (b := 𝟙 _)
    (intersectionRelative_square R A B)
    (fun j => by
      change IsIso (HomologicalComplex.homologyMap
        (intersectionRangeChainsToLiteral R A B).hom j)
      infer_instance)
    (fun j => by
      have h := HomologicalComplex.homologyMap_id
        ((CoefficientAmbientSubspaceRangeCompatibility.chains R).obj
          (TopCat.toSSet.obj (TopCat.of X))) j
      exact h.symm ▸ (IsIso.mk ⟨𝟙 _, rfl, rfl⟩)) n

#print axioms rangeRelativeIso
#print axioms intersectionRelativeIso
end ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso
