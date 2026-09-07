import ConstructionTargets.SardScalarizedJetKernelParameterContDiff

namespace SardImplicitFunctionKernelParameterCompositionContDiffProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Composing with the fixed-left-coordinate inverse chart preserves the same
pointwise smoothness order at the implicit-function base coordinate. -/
theorem ImplicitFunctionData.contDiffAt_comp_kernelParameter
    (φ : ImplicitFunctionData ℝ E ℝ G) {n : WithTop ℕ∞} (f : E → F)
    (hf : ContDiffAt ℝ n f φ.pt)
    (hparam : ContDiffAt ℝ n
      (fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z))
      (φ.rightFun φ.pt)) :
    ContDiffAt ℝ n
      (fun z : G => f (φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)))
      (φ.rightFun φ.pt) := by
  have heq : φ.toOpenPartialHomeomorph.symm
      (φ.leftFun φ.pt, φ.rightFun φ.pt) = φ.pt := by
    exact φ.toOpenPartialHomeomorph.leftInvOn φ.pt_mem_toOpenPartialHomeomorph_source
  have hf' : ContDiffAt ℝ n f
      (φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, φ.rightFun φ.pt)) := by
    simpa [heq] using hf
  exact hf'.comp (φ.rightFun φ.pt) hparam

#print axioms ImplicitFunctionData.contDiffAt_comp_kernelParameter
end SardImplicitFunctionKernelParameterCompositionContDiffProbe
