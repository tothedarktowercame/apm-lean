import ConstructionTargets.SardImplicitFunctionKernelParameterContDiff

namespace SardProjectedInverseChartSliceContDiffProbe

variable {E R G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- The fixed-left-coordinate inverse-chart slice of implicit-function data
has a Frechet derivative at its base kernel coordinate. -/
theorem ImplicitFunctionData.exists_hasFDerivAt_kernelParameter
    (φ : ImplicitFunctionData ℝ E R G)
    (hl : ContDiffAt ℝ 1 φ.leftFun φ.pt)
    (hr : ContDiffAt ℝ 1 φ.rightFun φ.pt) :
    ∃ J : G →L[ℝ] E,
      HasFDerivAt
        (fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)) J
        (φ.rightFun φ.pt) := by
  have hcd :=
    SardImplicitFunctionKernelParameterContDiffProbe.ImplicitFunctionData.contDiffAt_kernelParameter
      φ hl hr one_ne_zero
  exact ⟨_, (hcd.differentiableAt one_ne_zero).hasFDerivAt⟩

#print axioms ImplicitFunctionData.exists_hasFDerivAt_kernelParameter
end SardProjectedInverseChartSliceContDiffProbe
