import ConstructionTargets.SardNonzeroScalarDerivativeSplit
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Calculus.Implicit

noncomputable section
namespace SardNonzeroScalarImplicitFunctionDataProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A strictly differentiable scalar function whose derivative is nonzero on
one direction packages with the orthogonal projection onto its derivative
kernel as exact `ImplicitFunctionData`. -/
theorem exists_localChart_of_strictFDeriv_apply_ne_zero
    (g : E → ℝ) (x : E) (L : E →L[ℝ] ℝ)
    (hg : HasStrictFDerivAt g L x) {h : E} (hh : L h ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (ℝ × (L : E →ₗ[ℝ] ℝ).ker),
      x ∈ e.source ∧ e x = (g x, (L : E →ₗ[ℝ] ℝ).ker.orthogonalProjection x) := by
  let G := (L : E →ₗ[ℝ] ℝ).ker
  letI hfd : FiniteDimensional ℝ G :=
    FiniteDimensional.of_injective G.subtype G.injective_subtype
  letI hcs : CompleteSpace G := G.complete_of_finiteDimensional.completeSpace_coe
  let B : E →L[ℝ] G := G.orthogonalProjection
  have hL : L.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact SardNonzeroScalarDerivativeSurjectiveProbe.ContinuousLinearMap.surjective_of_apply_ne_zero
      L hh
  have hB : B.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨y, G.orthogonalProjection_mem_subspace_eq_self y⟩
  have hcompl : IsCompl L.ker B.ker := by
    rw [show B.ker = Gᗮ by
      change G.orthogonalProjection.ker = Gᗮ
      exact G.ker_orthogonalProjection]
    exact G.isCompl_orthogonal_of_hasOrthogonalProjection
  let φ := @ImplicitFunctionData.mk ℝ inferInstance E inferInstance inferInstance inferInstance
    ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance
    hcs
    g L (fun y => G.orthogonalProjection y) B x hg
    G.orthogonalProjection.hasStrictFDerivAt hL hB hcompl
  let e := @ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance
    inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance
    inferInstance hcs φ
  have hx := @ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source ℝ inferInstance E
    inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G
    inferInstance inferInstance hcs φ
  exact ⟨e, hx, rfl⟩

/-- The exact scalarized fixed-direction jet data packages as a local
implicit-function chart once its derivative is known to be strict. -/
theorem exists_localChart_scalar_fixedDirections
    (f : E → F) (i : ℕ) (x h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f)
    (hg : HasStrictFDerivAt (fun y => ℓ (iteratedFDeriv ℝ i f y v))
      (fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x) x)
    (hne : ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0) :
    let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x
    ∃ e : OpenPartialHomeomorph E (ℝ × (L : E →ₗ[ℝ] ℝ).ker),
      x ∈ e.source ∧
        e x = (ℓ (iteratedFDeriv ℝ i f x v),
          (L : E →ₗ[ℝ] ℝ).ker.orthogonalProjection x) := by
  dsimp only
  apply exists_localChart_of_strictFDeriv_apply_ne_zero _ _ _ hg (h := h)
  rw [SardNonzeroJetScalarDerivativeProbe.fderiv_scalar_fixedDirections_iteratedFDeriv_apply
    f i x h v ℓ hf]
  exact hne

#print axioms exists_localChart_of_strictFDeriv_apply_ne_zero
#print axioms exists_localChart_scalar_fixedDirections
end SardNonzeroScalarImplicitFunctionDataProbe
