import ConstructionTargets.SardProjectedInverseChartSliceContDiff
import ConstructionTargets.SardEventuallyConstantCoordinateSliceFlatness
import ConstructionTargets.SardProjectedInverseChartSliceConstancy

open Filter
open scoped Topology
namespace SardImplicitFunctionResidualSliceFlatnessProbe

variable {E R G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- A residual derivative vanishing on the left-coordinate kernel becomes zero
after restriction to the fixed-left-coordinate inverse-chart slice. -/
theorem ImplicitFunctionData.hasFDerivAt_zero_residual_kernelParameter
    (φ : ImplicitFunctionData ℝ E R G)
    (hl : ContDiffAt ℝ 1 φ.leftFun φ.pt)
    (hr : ContDiffAt ℝ 1 φ.rightFun φ.pt)
    (h : E → S) (H : E →L[ℝ] S)
    (hh : HasFDerivAt h H φ.pt)
    (hflat : ∀ v ∈ φ.leftDeriv.ker, H v = 0) :
    HasFDerivAt
      (h ∘ fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z))
      (0 : G →L[ℝ] S) (φ.rightFun φ.pt) := by
  obtain ⟨J, hJ⟩ :=
    SardProjectedInverseChartSliceContDiffProbe.ImplicitFunctionData.exists_hasFDerivAt_kernelParameter
      φ hl hr
  have hsbase :
      φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, φ.rightFun φ.pt) = φ.pt := by
    exact φ.toOpenPartialHomeomorph.leftInvOn φ.pt_mem_toOpenPartialHomeomorph_source
  apply SardEventuallyConstantCoordinateSliceFlatnessProbe.hasFDerivAt_zero_on_eventuallyConstantCoordinateSlice
    h φ.leftFun
    (fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z))
    (φ.leftFun φ.pt) (φ.rightFun φ.pt) H φ.leftDeriv J
  · simpa [hsbase] using hh
  · simpa [hsbase] using φ.hasStrictFDerivAt_leftFun.hasFDerivAt
  · exact hJ
  · apply SardProjectedInverseChartSliceConstancyProbe.eventually_firstCoordinate_inverse_fixedSlice
      (fun q : R × G => φ.implicitFunction q.1 q.2) φ.leftFun
      (φ.leftFun φ.pt) (φ.rightFun φ.pt)
      {q | φ.leftFun (φ.implicitFunction q.1 q.2) = q.1}
    · exact φ.leftFun_implicitFunction
    · intro q hq
      exact hq
  · exact hflat

#print axioms ImplicitFunctionData.hasFDerivAt_zero_residual_kernelParameter
end SardImplicitFunctionResidualSliceFlatnessProbe
