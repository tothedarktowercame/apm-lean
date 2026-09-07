import ConstructionTargets.SardScalarDerivativeKernelDimension

namespace SardScalarDerivativeKernelDimensionDropProbe

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A codimension-one scalar derivative kernel has strictly smaller finite
dimension than its source. -/
theorem ContinuousLinearMap.finrank_ker_lt_of_apply_ne_zero
    (L : E →L[ℝ] ℝ) {h : E} (hh : L h ≠ 0) :
    Module.finrank ℝ (L : E →ₗ[ℝ] ℝ).ker < Module.finrank ℝ E := by
  have hdim :=
    SardScalarDerivativeKernelDimensionProbe.ContinuousLinearMap.finrank_ker_add_one_of_apply_ne_zero
      L hh
  omega

/-- The scalarized fixed-direction jet chart reduces the source `finrank`
strictly under the selected nonzero next-jet hypothesis. -/
theorem finrank_ker_fderiv_scalar_fixedDirections_lt
    (f : E → F) (i : ℕ) (x h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f)
    (hne : ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0) :
    let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x
    Module.finrank ℝ (L : E →ₗ[ℝ] ℝ).ker < Module.finrank ℝ E := by
  dsimp only
  have hdim :=
    SardScalarDerivativeKernelDimensionProbe.finrank_ker_fderiv_scalar_fixedDirections_add_one
      f i x h v ℓ hf hne
  omega

#print axioms ContinuousLinearMap.finrank_ker_lt_of_apply_ne_zero
#print axioms finrank_ker_fderiv_scalar_fixedDirections_lt
end SardScalarDerivativeKernelDimensionDropProbe
