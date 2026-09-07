import ConstructionTargets.SardScalarizedJetStrictDerivative

noncomputable section
namespace SardScalarizedJetLocalChartProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A nonzero selected scalar component of the next jet gives local
implicit-function hypersurface coordinates for the fixed-direction jet. -/
theorem exists_localChart_scalar_fixedDirections_of_contDiff
    (f : E → F) (i : ℕ) (x h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f)
    (hne : ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0) :
    let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x
    ∃ e : OpenPartialHomeomorph E (ℝ × (L : E →ₗ[ℝ] ℝ).ker),
      x ∈ e.source ∧
        e x = (ℓ (iteratedFDeriv ℝ i f x v),
          (L : E →ₗ[ℝ] ℝ).ker.orthogonalProjection x) := by
  dsimp only
  exact SardNonzeroScalarImplicitFunctionDataProbe.exists_localChart_scalar_fixedDirections
    f i x h v ℓ hf
    (SardScalarizedJetStrictDerivativeProbe.hasStrictFDerivAt_scalar_fixedDirections_iteratedFDeriv
      f i x v ℓ hf)
    hne

#print axioms exists_localChart_scalar_fixedDirections_of_contDiff
end SardScalarizedJetLocalChartProbe
