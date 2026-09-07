import ConstructionTargets.SardNonzeroJetScalarSeparation

namespace SardNonzeroJetScalarDerivativeProbe

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of a fixed-direction scalar component of the `i`th
iterated Fréchet derivative is evaluation of the `(i+1)`st derivative with
the varying direction inserted first. -/
theorem hasFDerivAt_scalar_fixedDirections_iteratedFDeriv
    (f : E → F) (i : ℕ) (x : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f) :
    HasFDerivAt
      (fun y => ℓ (iteratedFDeriv ℝ i f y v))
      ((ℓ.comp (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E) F v)).comp
        (fderiv ℝ (iteratedFDeriv ℝ i f) x)) x := by
  let L : (E [×i]→L[ℝ] F) →L[ℝ] ℝ :=
    ℓ.comp (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E) F v)
  simpa [L] using L.hasFDerivAt.comp x
    ((hf.differentiable_iteratedFDeriv (by
      exact_mod_cast Nat.lt_succ_self i)).differentiableAt.hasFDerivAt)

/-- Pointwise form of the derivative identity for the selected scalar jet
component. -/
theorem fderiv_scalar_fixedDirections_iteratedFDeriv_apply
    (f : E → F) (i : ℕ) (x h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f) :
    fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x h =
      ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) := by
  rw [(hasFDerivAt_scalar_fixedDirections_iteratedFDeriv f i x v ℓ hf).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply]
  rw [iteratedFDeriv_succ_apply_left]
  rfl

#print axioms hasFDerivAt_scalar_fixedDirections_iteratedFDeriv
#print axioms fderiv_scalar_fixedDirections_iteratedFDeriv_apply
end SardNonzeroJetScalarDerivativeProbe
