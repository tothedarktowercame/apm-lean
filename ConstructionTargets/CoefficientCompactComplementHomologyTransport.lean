import ConstructionTargets.CoefficientCompactComplementPairHomeomorph
import ConstructionTargets.CoefficientH0

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementHomologyTransport

open CategoryTheory Set
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientCompactComplementSmallComparison
open ConstructionTargets.CoefficientCompactComplementPairHomeomorph

variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

abbrev chains := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj
  (ModuleCat.of R R)

noncomputable def leftChainsIso (K L : Set X) :
    CoefficientH0.SingularChains R (TopCat.of (left K L)) ≅
      CoefficientH0.SingularChains R (TopCat.of (Kᶜ : Set X)) :=
  (chains R).mapIso (TopCat.isoOfHomeo (leftHomeomorph K L))

noncomputable def rightChainsIso (K L : Set X) :
    CoefficientH0.SingularChains R (TopCat.of (right K L)) ≅
      CoefficientH0.SingularChains R (TopCat.of (Lᶜ : Set X)) :=
  (chains R).mapIso (TopCat.isoOfHomeo (rightHomeomorph K L))

noncomputable def overlapChainsIso (K L : Set X) :
    CoefficientH0.SingularChains R (TopCat.of (overlap K L)) ≅
      CoefficientH0.SingularChains R (TopCat.of ((K ∪ L)ᶜ : Set X)) :=
  (chains R).mapIso (TopCat.isoOfHomeo (overlapHomeomorph K L))

noncomputable def leftHomologyIso (K L : Set X) (n : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (leftChainsIso R K L)

noncomputable def rightHomologyIso (K L : Set X) (n : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (rightChainsIso R K L)

noncomputable def overlapHomologyIso (K L : Set X) (n : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (overlapChainsIso R K L)

def nestedLeftInclusion (K L : Set X) : C(left K L, X) :=
  ⟨fun x => x.1.1, continuous_subtype_val.comp continuous_subtype_val⟩

def originalLeftInclusion (K : Set X) : C((Kᶜ : Set X), X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def nestedRightInclusion (K L : Set X) : C(right K L, X) :=
  ⟨fun x => x.1.1, continuous_subtype_val.comp continuous_subtype_val⟩

def originalRightInclusion (L : Set X) : C((Lᶜ : Set X), X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def nestedOverlapInclusion (K L : Set X) : C((overlap K L : Set (ambient K L)), X) :=
  ⟨fun x => x.1.1, continuous_subtype_val.comp continuous_subtype_val⟩

def originalOverlapInclusion (K L : Set X) : C(((K ∪ L)ᶜ : Set X), X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem left_inclusion_comp (K L : Set X) :
    (originalLeftInclusion K).comp (⟨leftHomeomorph K L, (leftHomeomorph K L).continuous⟩ : C(left K L, (Kᶜ : Set X))) =
      nestedLeftInclusion K L := by ext x; rfl

theorem right_inclusion_comp (K L : Set X) :
    (originalRightInclusion L).comp (⟨rightHomeomorph K L, (rightHomeomorph K L).continuous⟩ : C(right K L, (Lᶜ : Set X))) =
      nestedRightInclusion K L := by ext x; rfl

theorem overlap_inclusion_comp (K L : Set X) :
    (originalOverlapInclusion K L).comp (⟨overlapHomeomorph K L, (overlapHomeomorph K L).continuous⟩ : C((overlap K L : Set (ambient K L)), ((K ∪ L)ᶜ : Set X))) =
      nestedOverlapInclusion K L := by ext x; rfl

#print axioms leftChainsIso
#print axioms rightChainsIso
#print axioms overlapChainsIso
#print axioms leftHomologyIso
#print axioms rightHomologyIso
#print axioms overlapHomologyIso
#print axioms left_inclusion_comp
#print axioms right_inclusion_comp
#print axioms overlap_inclusion_comp

end ConstructionTargets.CoefficientCompactComplementHomologyTransport
