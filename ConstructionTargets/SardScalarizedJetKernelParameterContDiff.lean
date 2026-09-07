import ConstructionTargets.SardScalarizedJetRemainingOrderContDiff
import ConstructionTargets.SardScalarImplicitFunctionDataDefiningFields

noncomputable section
namespace SardScalarizedJetKernelParameterContDiffProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The exact scalarized-jet implicit-function data may be chosen so that its
kernel parameter retains any separately supplied remaining smoothness order. -/
theorem exists_implicitFunctionData_scalar_fixedDirections_kernelParameter_contDiffAt
    (f : E → F) (i : ℕ) (n : WithTop ℕ∞) (x h : E)
    (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf1 : ContDiff ℝ (i + 1) f) (hfn : ContDiff ℝ (n + i) f) (hn : n ≠ 0)
    (hne : ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0) :
    let g := fun y => ℓ (iteratedFDeriv ℝ i f y v)
    let L := fderiv ℝ g x
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
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = x ∧
      ContDiffAt ℝ n
        (fun z : G =>
          (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance
            inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G
            inferInstance inferInstance hG φ).symm
            ((@ImplicitFunctionData.leftFun ℝ inferInstance E inferInstance inferInstance
              inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance
              inferInstance hG φ)
              (@ImplicitFunctionData.pt ℝ inferInstance E inferInstance inferInstance inferInstance
                ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ), z))
        ((@ImplicitFunctionData.rightFun ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ)
          (@ImplicitFunctionData.pt ℝ inferInstance E inferInstance inferInstance inferInstance
            ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ)) := by
  dsimp only
  let g := fun y => ℓ (iteratedFDeriv ℝ i f y v)
  let L := fderiv ℝ g x
  let G := (L : E →ₗ[ℝ] ℝ).ker
  letI hG : CompleteSpace G :=
    SardScalarizedJetImplicitFunctionDataProbe.kernelCompleteSpace L
  have hs : HasStrictFDerivAt g L x := by
    exact SardScalarizedJetStrictDerivativeProbe.hasStrictFDerivAt_scalar_fixedDirections_iteratedFDeriv
      f i x v ℓ hf1
  have hLh : L h ≠ 0 := by
    rw [SardNonzeroJetScalarDerivativeProbe.fderiv_scalar_fixedDirections_iteratedFDeriv_apply
      f i x h v ℓ hf1]
    exact hne
  obtain ⟨φ, hleft, hderiv, hright, hrightDeriv, hpt⟩ :=
    SardScalarImplicitFunctionDataDefiningFieldsProbe.exists_implicitFunctionData_with_defining_fields
      g x L hs hLh
  refine ⟨φ, hleft, hderiv, hright, hrightDeriv, hpt, ?_⟩
  exact @SardScalarImplicitFunctionKernelParameterContDiffProbe.ImplicitFunctionData.contDiffAt_kernelParameter_of_definingFields
    E G inferInstance inferInstance inferInstance inferInstance inferInstance hG
    φ n g G.orthogonalProjection x hleft hright hpt
    (SardScalarizedJetRemainingOrderContDiffProbe.contDiffAt_scalar_fixedDirections_iteratedFDeriv_remainingOrder
      f i n x v ℓ hfn) hn

#print axioms exists_implicitFunctionData_scalar_fixedDirections_kernelParameter_contDiffAt
end SardScalarizedJetKernelParameterContDiffProbe
