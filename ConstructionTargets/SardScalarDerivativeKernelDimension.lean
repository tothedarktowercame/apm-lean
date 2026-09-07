import ConstructionTargets.SardScalarizedJetLocalChart
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace SardScalarDerivativeKernelDimensionProbe

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The kernel of a scalar continuous linear map that is nonzero on one
direction has codimension exactly one. -/
theorem ContinuousLinearMap.finrank_ker_add_one_of_apply_ne_zero
    (L : E →L[ℝ] ℝ) {h : E} (hh : L h ≠ 0) :
    Module.finrank ℝ (L : E →ₗ[ℝ] ℝ).ker + 1 = Module.finrank ℝ E := by
  apply Module.Dual.finrank_ker_add_one_of_ne_zero
  intro hzero
  apply hh
  exact DFunLike.congr_fun hzero h

/-- The derivative kernel in the scalarized fixed-direction jet chart has
codimension exactly one under the selected nonzero next-jet hypothesis. -/
theorem finrank_ker_fderiv_scalar_fixedDirections_add_one
    (f : E → F) (i : ℕ) (x h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f)
    (hne : ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0) :
    let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x
    Module.finrank ℝ (L : E →ₗ[ℝ] ℝ).ker + 1 = Module.finrank ℝ E := by
  dsimp only
  apply ContinuousLinearMap.finrank_ker_add_one_of_apply_ne_zero _ (h := h)
  rw [SardNonzeroJetScalarDerivativeProbe.fderiv_scalar_fixedDirections_iteratedFDeriv_apply
    f i x h v ℓ hf]
  exact hne

#print axioms ContinuousLinearMap.finrank_ker_add_one_of_apply_ne_zero
#print axioms finrank_ker_fderiv_scalar_fixedDirections_add_one
end SardScalarDerivativeKernelDimensionProbe
