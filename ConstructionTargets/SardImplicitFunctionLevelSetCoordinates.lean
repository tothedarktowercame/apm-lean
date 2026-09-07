import ConstructionTargets.SardScalarDerivativeKernelDimensionDrop
import Mathlib.Analysis.Calculus.Implicit

namespace SardImplicitFunctionLevelSetCoordinatesProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- In implicit-function coordinates, equality of the left function to a
value is exactly equality of the first chart coordinate to that value. -/
theorem ImplicitFunctionData.leftFun_eq_iff_fst_toOpenPartialHomeomorph_eq
    (φ : ImplicitFunctionData ℝ E F G) (y : E) (c : F) :
    φ.leftFun y = c ↔ (φ.toOpenPartialHomeomorph y).1 = c := by
  rw [φ.toOpenPartialHomeomorph_apply]

/-- Localizing to the chart source preserves the exact description of a left
level set as a constant-first-coordinate slice. -/
theorem ImplicitFunctionData.inter_source_leftFun_level_eq
    (φ : ImplicitFunctionData ℝ E F G) (c : F) :
    φ.toOpenPartialHomeomorph.source ∩ {y | φ.leftFun y = c} =
      φ.toOpenPartialHomeomorph.source ∩ {y | (φ.toOpenPartialHomeomorph y).1 = c} := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [φ.toOpenPartialHomeomorph_apply]

#print axioms ImplicitFunctionData.leftFun_eq_iff_fst_toOpenPartialHomeomorph_eq
#print axioms ImplicitFunctionData.inter_source_leftFun_level_eq
end SardImplicitFunctionLevelSetCoordinatesProbe
