import ConstructionTargets.SardImplicitFunctionLevelSetCoordinates
import ConstructionTargets.SardScalarizedJetStrictDerivative
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Calculus.Implicit

noncomputable section
namespace SardScalarizedJetImplicitFunctionDataProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

@[reducible] noncomputable def kernelCompleteSpace (L : E →L[ℝ] ℝ) :
    CompleteSpace (L : E →ₗ[ℝ] ℝ).ker := by
  letI : FiniteDimensional ℝ (L : E →ₗ[ℝ] ℝ).ker :=
    FiniteDimensional.of_injective (L : E →ₗ[ℝ] ℝ).ker.subtype
      (L : E →ₗ[ℝ] ℝ).ker.injective_subtype
  exact (L : E →ₗ[ℝ] ℝ).ker.complete_of_finiteDimensional.completeSpace_coe

/-- A scalar strict derivative nonzero on one direction gives exact
`ImplicitFunctionData`, retaining its defining left function and derivative. -/
theorem exists_implicitFunctionData_of_strictFDeriv_apply_ne_zero
    (g : E → ℝ) (x : E) (L : E →L[ℝ] ℝ)
    (hg : HasStrictFDerivAt g L x) {h : E} (hh : L h ≠ 0) :
    let G := (L : E →ₗ[ℝ] ℝ).ker
    let hG : CompleteSpace G := kernelCompleteSpace L
    ∃ φ : @ImplicitFunctionData ℝ inferInstance E inferInstance inferInstance inferInstance
        ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG,
      (@ImplicitFunctionData.leftFun ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = g ∧
        (@ImplicitFunctionData.leftDeriv ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = L ∧
        x ∈ (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance
          inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance
          inferInstance hG φ).source := by
  dsimp only
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
    ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hcs
    g L (fun y => G.orthogonalProjection y) B x hg
    G.orthogonalProjection.hasStrictFDerivAt hL hB hcompl
  exact ⟨φ, rfl, rfl,
    @ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source ℝ inferInstance E
      inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G
      inferInstance inferInstance hcs φ⟩

/-- The selected scalarized fixed-direction jet gives exact implicit-function
data directly from its `ContDiff` and nonzero next-jet hypotheses. -/
theorem exists_implicitFunctionData_scalar_fixedDirections_of_contDiff
    (f : E → F) (i : ℕ) (x h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ (i + 1) f)
    (hne : ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0) :
    let g := fun y => ℓ (iteratedFDeriv ℝ i f y v)
    let L := fderiv ℝ g x
    let G := (L : E →ₗ[ℝ] ℝ).ker
    let hG : CompleteSpace G := kernelCompleteSpace L
    ∃ φ : @ImplicitFunctionData ℝ inferInstance E inferInstance inferInstance inferInstance
        ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG,
      (@ImplicitFunctionData.leftFun ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = g ∧
        (@ImplicitFunctionData.leftDeriv ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = L ∧
        x ∈ (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance
          inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance
          inferInstance hG φ).source := by
  dsimp only
  apply exists_implicitFunctionData_of_strictFDeriv_apply_ne_zero _ _ _
    (SardScalarizedJetStrictDerivativeProbe.hasStrictFDerivAt_scalar_fixedDirections_iteratedFDeriv
      f i x v ℓ hf) (h := h)
  rw [SardNonzeroJetScalarDerivativeProbe.fderiv_scalar_fixedDirections_iteratedFDeriv_apply
    f i x h v ℓ hf]
  exact hne

#print axioms exists_implicitFunctionData_of_strictFDeriv_apply_ne_zero
#print axioms exists_implicitFunctionData_scalar_fixedDirections_of_contDiff
end SardScalarizedJetImplicitFunctionDataProbe
