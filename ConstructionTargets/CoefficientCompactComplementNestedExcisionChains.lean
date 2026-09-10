import ConstructionTargets.CoefficientCompactComplementPairHomeomorph
import ConstructionTargets.CoefficientCompactComplementNestedExcisionSource
import ConstructionTargets.CoefficientOverlapNormalization
noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementNestedExcisionChains
open ConstructionTargets.SingularExcision
open ConstructionTargets.NestedSubspaceIntersectionComparison
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientCompactComplementPairHomeomorph
open ConstructionTargets.CoefficientOverlapNormalization
variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]

theorem nestedRightToExcised_mem (K L : Set X) (y : right K L) :
    rightHomeomorph K L y ∈ excisedSubspace (Kᶜ) L ↔
      y ∈ nestedIntersection (left K L) (right K L) := by rfl

noncomputable def nestedRightRelativeChainsIso (K L : Set X) :
    CoefficientRelativeSmall.relativeChains R
        (nestedIntersection (left K L) (right K L)) ≅
      CoefficientRelativeSmall.relativeChains R (excisedSubspace (Kᶜ) L) :=
  pairHomeo R (rightHomeomorph K L)
    (nestedIntersection (left K L) (right K L)) (excisedSubspace (Kᶜ) L)
    (nestedRightToExcised_mem K L)

#print axioms nestedRightToExcised_mem
#print axioms nestedRightRelativeChainsIso
end ConstructionTargets.CoefficientCompactComplementNestedExcisionChains
