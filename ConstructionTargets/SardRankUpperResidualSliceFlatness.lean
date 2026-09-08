import ConstructionTargets.SardImplicitFunctionResidualSliceFlatness
import ConstructionTargets.SardLocalResidualDerivativeFlatness

namespace SardRankUpperResidualSliceFlatnessProbe

variable {E F R G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Rank-at-most residual flatness supplies the kernel hypothesis needed to
make the residual map flat on the fixed-coordinate inverse-chart slice. -/
theorem ImplicitFunctionData.hasFDerivAt_zero_residual_kernelParameter_of_rankUpper
    (φ : ImplicitFunctionData ℝ E R G)
    (D : E → (E →ₗ[ℝ] F)) (P : F →ₗ[ℝ] R) (Q : F →ₗ[ℝ] S) (U : Set E)
    (hpt : φ.pt ∈ U)
    (hsurj : ∀ y ∈ U, (P.comp (D y)).range = ⊤)
    (hrank : ∀ y ∈ U,
      Module.finrank ℝ (LinearMap.range (D y)) ≤ Module.finrank ℝ R)
    (hleft : φ.leftDeriv.toLinearMap = P.comp (D φ.pt))
    (hl : ContDiffAt ℝ 1 φ.leftFun φ.pt)
    (hr : ContDiffAt ℝ 1 φ.rightFun φ.pt)
    (h : E → S)
    (hh : HasFDerivAt h ((Q.comp (D φ.pt)).toContinuousLinearMap) φ.pt) :
    HasFDerivAt
      (h ∘ fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z))
      (0 : G →L[ℝ] S) (φ.rightFun φ.pt) := by
  apply SardImplicitFunctionResidualSliceFlatnessProbe.ImplicitFunctionData.hasFDerivAt_zero_residual_kernelParameter
    φ hl hr h ((Q.comp (D φ.pt)).toContinuousLinearMap) hh
  intro v hv
  apply SardLocalResidualDerivativeFlatnessProbe.residualDerivative_vanishes_on_projectedFibres
    D P Q U hsurj hrank φ.pt hpt v
  rw [← hleft]
  exact hv

#print axioms ImplicitFunctionData.hasFDerivAt_zero_residual_kernelParameter_of_rankUpper
end SardRankUpperResidualSliceFlatnessProbe
