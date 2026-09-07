import Mathlib.Analysis.Calculus.Implicit

namespace SardImplicitFunctionResidualFlatnessProbe

variable {E R G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- A residual derivative that vanishes on the regular-coordinate kernel has
zero derivative after restriction to Mathlib's exact implicit-function slice. -/
theorem hasFDerivAt_residual_comp_implicitFunction_zero
    (φ : ImplicitFunctionData ℝ E R G) (h : E → S) (H : E →L[ℝ] S)
    (hh : HasFDerivAt h H φ.pt)
    (hflat : ∀ v ∈ φ.leftDeriv.ker, H v = 0) :
    HasFDerivAt
      (h ∘ φ.implicitFunction (φ.leftFun φ.pt)) (0 : G →L[ℝ] S)
      (φ.rightFun φ.pt) := by
  let J := fderiv ℝ (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt)
  have hs : HasFDerivAt (φ.implicitFunction (φ.leftFun φ.pt)) J
      (φ.rightFun φ.pt) := φ.hasStrictFDerivAt_implicitFunction_fderiv.hasFDerivAt
  have hHJ : H.comp J = 0 := by
    ext v
    have hv : J v ∈ φ.leftDeriv.ker := by
      change φ.leftDeriv (J v) = 0
      exact φ.leftDeriv_fderiv_implicitFunction v
    simpa using hflat (J v) hv
  have heq : φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun φ.pt) = φ.pt :=
    φ.implicitFunction_apply_image.self_of_nhds
  have hh' : HasFDerivAt h H
      (φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun φ.pt)) := by simpa [heq] using hh
  have hc := hh'.comp (φ.rightFun φ.pt) hs
  simpa [hHJ] using hc

#print axioms hasFDerivAt_residual_comp_implicitFunction_zero
end SardImplicitFunctionResidualFlatnessProbe
