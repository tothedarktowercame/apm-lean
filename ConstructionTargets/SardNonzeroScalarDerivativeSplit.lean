import ConstructionTargets.SardNonzeroScalarDerivativeSurjective

namespace SardNonzeroScalarDerivativeSplitProbe

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A nonzero direction for a scalar continuous linear map gives an explicit
continuous linear right inverse. -/
theorem ContinuousLinearMap.exists_rightInverse_of_apply_ne_zero
    (L : E →L[ℝ] ℝ) {h : E} (hh : L h ≠ 0) :
    ∃ R : ℝ →L[ℝ] E, Function.RightInverse R L := by
  let R : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight
    ((L h)⁻¹ • ContinuousLinearMap.id ℝ ℝ) h
  refine ⟨R, fun y => ?_⟩
  simp only [R, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.map_smul]
  calc
    (L h)⁻¹ * y * L h = y * ((L h)⁻¹ * L h) := by ring
    _ = y := by rw [inv_mul_cancel₀ hh, mul_one]

/-- The explicit right inverse also supplies the canonical continuous linear
projection onto the kernel. -/
theorem ContinuousLinearMap.exists_rightInverse_and_projKer_of_apply_ne_zero
    (L : E →L[ℝ] ℝ) {h : E} (hh : L h ≠ 0) :
    ∃ (R : ℝ →L[ℝ] E) (hR : Function.RightInverse R L)
      (P : E →L[ℝ] (L : E →ₗ[ℝ] ℝ).ker),
        P = ContinuousLinearMap.projKerOfRightInverse L R hR := by
  obtain ⟨R, hR⟩ :=
    ContinuousLinearMap.exists_rightInverse_of_apply_ne_zero L hh
  exact ⟨R, hR, ContinuousLinearMap.projKerOfRightInverse L R hR, rfl⟩

/-- The selected nonzero next-jet value supplies explicit split derivative
data for the fixed-direction scalar jet component. -/
theorem exists_rightInverse_and_projKer_fderiv_scalar_fixedDirections
    (f : E → F) (i : ℕ) (x h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f)
    (hne : ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0) :
    let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x
    ∃ (R : ℝ →L[ℝ] E) (hR : Function.RightInverse R L)
      (P : E →L[ℝ] (L : E →ₗ[ℝ] ℝ).ker),
        P = ContinuousLinearMap.projKerOfRightInverse L R hR := by
  dsimp only
  apply ContinuousLinearMap.exists_rightInverse_and_projKer_of_apply_ne_zero _ (h := h)
  rw [SardNonzeroJetScalarDerivativeProbe.fderiv_scalar_fixedDirections_iteratedFDeriv_apply
    f i x h v ℓ hf]
  exact hne

#print axioms ContinuousLinearMap.exists_rightInverse_of_apply_ne_zero
#print axioms ContinuousLinearMap.exists_rightInverse_and_projKer_of_apply_ne_zero
#print axioms exists_rightInverse_and_projKer_fderiv_scalar_fixedDirections
end SardNonzeroScalarDerivativeSplitProbe
