import ConstructionTargets.SardNonzeroScalarImplicitFunctionData
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace SardScalarizedJetStrictDerivativeProbe

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fixed-direction scalar component of the `i`th iterated Fréchet
derivative is continuously differentiable when the original map is `C^(i+1)`. -/
theorem contDiff_one_scalar_fixedDirections_iteratedFDeriv
    (f : E → F) (i : ℕ) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f) :
    ContDiff ℝ 1 (fun y => ℓ (iteratedFDeriv ℝ i f y v)) := by
  have hi : ContDiff ℝ 1 (iteratedFDeriv ℝ i f) :=
    (show ContDiff ℝ (1 + i) f by simpa [add_comm] using hf).iteratedFDeriv_right'
  have hev : ContDiff ℝ 1 (fun y => iteratedFDeriv ℝ i f y v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E) F v).contDiff.comp hi
  exact ℓ.contDiff.comp hev

/-- The scalarized fixed-direction jet has its `fderiv` as strict derivative
under the exact `C^(i+1)` regularity bound. -/
theorem hasStrictFDerivAt_scalar_fixedDirections_iteratedFDeriv
    (f : E → F) (i : ℕ) (x : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f) :
    HasStrictFDerivAt (fun y => ℓ (iteratedFDeriv ℝ i f y v))
      (fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x) x := by
  exact (contDiff_one_scalar_fixedDirections_iteratedFDeriv f i v ℓ hf).hasStrictFDerivAt
    one_ne_zero

#print axioms contDiff_one_scalar_fixedDirections_iteratedFDeriv
#print axioms hasStrictFDerivAt_scalar_fixedDirections_iteratedFDeriv
end SardScalarizedJetStrictDerivativeProbe
