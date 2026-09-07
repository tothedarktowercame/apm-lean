import ConstructionTargets.SardNonzeroJetScalarDerivative

namespace SardNonzeroScalarDerivativeSurjectiveProbe

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A real-valued linear map that is nonzero on one direction is surjective. -/
theorem ContinuousLinearMap.surjective_of_apply_ne_zero
    (L : E →L[ℝ] ℝ) {h : E} (hh : L h ≠ 0) : Function.Surjective L := by
  intro y
  refine ⟨(y / L h) • h, ?_⟩
  simp [hh]

/-- A nonzero value of the next iterated derivative makes the derivative of
the corresponding fixed-direction scalar jet component surjective. -/
theorem surjective_fderiv_scalar_fixedDirections_iteratedFDeriv
    (f : E → F) (i : ℕ) (x h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f)
    (hne : ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0) :
    Function.Surjective
      (fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x) := by
  apply ContinuousLinearMap.surjective_of_apply_ne_zero _ (h := h)
  rwa [SardNonzeroJetScalarDerivativeProbe.fderiv_scalar_fixedDirections_iteratedFDeriv_apply
    f i x h v ℓ hf]

#print axioms ContinuousLinearMap.surjective_of_apply_ne_zero
#print axioms surjective_fderiv_scalar_fixedDirections_iteratedFDeriv
end SardNonzeroScalarDerivativeSurjectiveProbe
