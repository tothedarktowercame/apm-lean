import ConstructionTargets.SardFirstNonzeroJetKernelParameterContainment
import ConstructionTargets.SardScalarizedJetKernelParameterContDiff

open Set

namespace SardImplicitFunctionKernelParameterLocalRegularityProbe

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Pointwise smoothness of the exact inverse-chart kernel parameter yields an
open parameter neighborhood on which the same map is smooth, hence
differentiable, at every point. -/
theorem ImplicitFunctionData.exists_open_kernelParameter_contDiffAt_and_differentiableAt
    (φ : ImplicitFunctionData ℝ E ℝ G) (n : WithTop ℕ∞)
    (hnTop : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (hn0 : n ≠ 0)
    (h : ContDiffAt ℝ n
      (fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z))
      (φ.rightFun φ.pt)) :
    ∃ V : Set G,
      IsOpen V ∧ φ.rightFun φ.pt ∈ V ∧
      ∀ z ∈ V,
        ContDiffAt ℝ n
          (fun w : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, w)) z ∧
        DifferentiableAt ℝ
          (fun w : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, w)) z := by
  obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp (h.eventually hnTop)
  refine ⟨V, hVopen, hzV, ?_⟩
  intro z hz
  have hzcd := hVsub hz
  exact ⟨hzcd, hzcd.differentiableAt hn0⟩

#print axioms ImplicitFunctionData.exists_open_kernelParameter_contDiffAt_and_differentiableAt
end SardImplicitFunctionKernelParameterLocalRegularityProbe
