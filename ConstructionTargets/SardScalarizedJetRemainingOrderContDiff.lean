import ConstructionTargets.SardScalarImplicitFunctionKernelParameterContDiff

namespace SardScalarizedJetRemainingOrderContDiffProbe

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Fixing all multilinear directions and applying a continuous scalar
functional preserves the full differentiability order remaining after taking
the `i`th iterated derivative. -/
theorem contDiff_scalar_fixedDirections_iteratedFDeriv_remainingOrder
    (f : E → F) (i : ℕ) (n : WithTop ℕ∞) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (n + i) f) :
    ContDiff ℝ n (fun y => ℓ (iteratedFDeriv ℝ i f y v)) := by
  have hi : ContDiff ℝ n (iteratedFDeriv ℝ i f) := hf.iteratedFDeriv_right'
  have hev : ContDiff ℝ n (fun y => iteratedFDeriv ℝ i f y v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E) F v).contDiff.comp hi
  exact ℓ.contDiff.comp hev

/-- Pointwise form of the remaining-order scalarized-jet regularity theorem. -/
theorem contDiffAt_scalar_fixedDirections_iteratedFDeriv_remainingOrder
    (f : E → F) (i : ℕ) (n : WithTop ℕ∞) (x : E)
    (v : Fin i → E) (ℓ : F →L[ℝ] ℝ) (hf : ContDiff ℝ (n + i) f) :
    ContDiffAt ℝ n (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x :=
  (contDiff_scalar_fixedDirections_iteratedFDeriv_remainingOrder f i n v ℓ hf).contDiffAt

#print axioms contDiff_scalar_fixedDirections_iteratedFDeriv_remainingOrder
#print axioms contDiffAt_scalar_fixedDirections_iteratedFDeriv_remainingOrder
end SardScalarizedJetRemainingOrderContDiffProbe
