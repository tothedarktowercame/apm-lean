import ConstructionTargets.CoefficientUnionToProductionRelativeComparison
import ConstructionTargets.CoefficientCompactComplementCoverSequence
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementUnionToRelative
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientUnionToProductionRelativeComparison
open ConstructionTargets.NestedSubspaceIntersectionComparison
variable (R : Type) [CommRing R]
variable {X : Type} [TopologicalSpace X]
noncomputable def compactUnionToRelative (K L : Set X) :=
  unionToProductionRelative R (left K L) (right K L)
#print axioms compactUnionToRelative
end ConstructionTargets.CoefficientCompactComplementUnionToRelative
