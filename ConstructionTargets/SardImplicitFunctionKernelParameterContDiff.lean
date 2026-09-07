import ConstructionTargets.SardImplicitFunctionLevelSetKernelParameterization
import Mathlib.Analysis.Calculus.ImplicitContDiff

namespace SardImplicitFunctionKernelParameterContDiffProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- If both defining functions of exact implicit-function data are `C^n` at
the base point, then its fixed-left-coordinate kernel parameterization is
`C^n` at the right coordinate of that point. -/
theorem ImplicitFunctionData.contDiffAt_kernelParameter
    (φ : ImplicitFunctionData ℝ E F G) {n : WithTop ℕ∞}
    (hl : ContDiffAt ℝ n φ.leftFun φ.pt)
    (hr : ContDiffAt ℝ n φ.rightFun φ.pt) (hn : n ≠ 0) :
    ContDiffAt ℝ n
      (fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z))
      (φ.rightFun φ.pt) := by
  have h := φ.contDiffAt_implicitFunction hl hr hn
  change ContDiffAt ℝ n (fun z : G => φ.implicitFunction (φ.leftFun φ.pt) z)
    (φ.rightFun φ.pt)
  fun_prop

#print axioms ImplicitFunctionData.contDiffAt_kernelParameter
end SardImplicitFunctionKernelParameterContDiffProbe
