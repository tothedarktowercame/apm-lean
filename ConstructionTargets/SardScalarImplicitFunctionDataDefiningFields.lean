import ConstructionTargets.SardImplicitFunctionKernelParameterContDiff
import ConstructionTargets.SardScalarizedJetImplicitFunctionData

noncomputable section
namespace SardScalarImplicitFunctionDataDefiningFieldsProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- The scalar implicit-function construction can be chosen with every
defining field exposed, including its orthogonal-projection right coordinate. -/
theorem exists_implicitFunctionData_with_defining_fields
    (g : E → ℝ) (x : E) (L : E →L[ℝ] ℝ)
    (hg : HasStrictFDerivAt g L x) {h : E} (hh : L h ≠ 0) :
    let G := (L : E →ₗ[ℝ] ℝ).ker
    let hG : CompleteSpace G :=
      SardScalarizedJetImplicitFunctionDataProbe.kernelCompleteSpace L
    ∃ φ : @ImplicitFunctionData ℝ inferInstance E inferInstance inferInstance inferInstance
        ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG,
      (@ImplicitFunctionData.leftFun ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = g ∧
      (@ImplicitFunctionData.leftDeriv ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = L ∧
      (@ImplicitFunctionData.rightFun ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) =
        (fun y => G.orthogonalProjection y) ∧
      (@ImplicitFunctionData.rightDeriv ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) =
        G.orthogonalProjection ∧
      (@ImplicitFunctionData.pt ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = x := by
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
  exact ⟨φ, rfl, rfl, rfl, rfl, rfl⟩

#print axioms exists_implicitFunctionData_with_defining_fields
end SardScalarImplicitFunctionDataDefiningFieldsProbe
