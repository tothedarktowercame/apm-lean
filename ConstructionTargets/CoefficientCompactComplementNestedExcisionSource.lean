import ConstructionTargets.CoefficientCompactComplementUnionRelativeFormulas
import ConstructionTargets.CoefficientExcision
open CategoryTheory
noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementNestedExcisionSource
open Set
open ConstructionTargets.SingularExcision
open ConstructionTargets.NestedSubspaceIntersectionComparison
open ConstructionTargets.CoefficientCompactComplementGeometry
variable {X : Type} [TopologicalSpace X]

def nestedRightToExcised (K L : Set X) :
    nestedIntersection (left K L) (right K L) ≃ₜ excisedSubspace (Lᶜ) K where
  toFun x := ⟨⟨x.1.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨⟨x.1.1, fun h => x.1.2 h.1⟩, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

#print axioms nestedRightToExcised
end ConstructionTargets.CoefficientCompactComplementNestedExcisionSource
