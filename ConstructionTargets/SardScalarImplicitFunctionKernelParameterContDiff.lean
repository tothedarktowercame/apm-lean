import ConstructionTargets.SardScalarImplicitFunctionDataDefiningFields

namespace SardScalarImplicitFunctionKernelParameterContDiffProbe

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Exposed defining fields reduce smoothness of the exact implicit-function
kernel parameter to smoothness of the scalar function; a continuous-linear
right coordinate is smooth in every order. -/
theorem ImplicitFunctionData.contDiffAt_kernelParameter_of_definingFields
    (φ : ImplicitFunctionData ℝ E ℝ G) {n : WithTop ℕ∞}
    (g : E → ℝ) (B : E →L[ℝ] G) (x : E)
    (hleft : φ.leftFun = g) (hright : φ.rightFun = B) (hpt : φ.pt = x)
    (hg : ContDiffAt ℝ n g x) (hn : n ≠ 0) :
    ContDiffAt ℝ n
      (fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z))
      (φ.rightFun φ.pt) := by
  apply SardImplicitFunctionKernelParameterContDiffProbe.ImplicitFunctionData.contDiffAt_kernelParameter
  · simpa [hleft, hpt] using hg
  · rw [hright]
    exact B.contDiff.contDiffAt
  · exact hn

#print axioms ImplicitFunctionData.contDiffAt_kernelParameter_of_definingFields
end SardScalarImplicitFunctionKernelParameterContDiffProbe
