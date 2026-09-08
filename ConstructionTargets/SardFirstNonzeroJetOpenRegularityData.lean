import ConstructionTargets.SardImplicitFunctionKernelParameterLocalRegularity
import ConstructionTargets.SardNonzeroSuccessorJetScalarDirections
import ConstructionTargets.SardScalarizedJetKernelParameterContDiff
import ConstructionTargets.SardScalarDerivativeKernelDimensionDrop

noncomputable section
namespace SardFirstNonzeroJetOpenRegularityDataProbe

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A nonzero successor jet packages the selected scalar directions together
with exact scalarized implicit-chart data, kernel smoothness, and dimension drop. -/
theorem exists_scalarizedJet_openRegularityData
    (f : E → F) (i : ℕ) (n : WithTop ℕ∞) (x : E)
    (hf1 : ContDiff ℝ (i + 1) f) (hfn : ContDiff ℝ (n + i) f) (hn : n ≠ 0)
    (hnTop : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hx : iteratedFDeriv ℝ (i + 1) f x ≠ 0) :
    ∃ (h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ),
      ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0 ∧
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
        (@ImplicitFunctionData.pt ℝ inferInstance E inferInstance inferInstance inferInstance
          ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = x ∧
        Module.finrank ℝ G < Module.finrank ℝ E ∧
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
              ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ)) ∧
        ∃ V : Set G, IsOpen V ∧
          (@ImplicitFunctionData.rightFun ℝ inferInstance E inferInstance inferInstance inferInstance
            ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ)
            (@ImplicitFunctionData.pt ℝ inferInstance E inferInstance inferInstance inferInstance
              ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) ∈ V ∧
          ∀ z ∈ V,
            ContDiffAt ℝ n
              (fun w : G =>
                (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance
                  inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G
                  inferInstance inferInstance hG φ).symm
                  ((@ImplicitFunctionData.leftFun ℝ inferInstance E inferInstance inferInstance
                    inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance
                    inferInstance hG φ)
                    (@ImplicitFunctionData.pt ℝ inferInstance E inferInstance inferInstance inferInstance
                      ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ), w)) z ∧
            DifferentiableAt ℝ
              (fun w : G =>
                (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance
                  inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G
                  inferInstance inferInstance hG φ).symm
                  ((@ImplicitFunctionData.leftFun ℝ inferInstance E inferInstance inferInstance
                    inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance
                    inferInstance hG φ)
                    (@ImplicitFunctionData.pt ℝ inferInstance E inferInstance inferInstance inferInstance
                      ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ), w)) z := by
  obtain ⟨h, v, ℓ, hne⟩ :=
    SardNonzeroSuccessorJetScalarDirectionsProbe.exists_firstDirection_tail_scalar_apply_ne_zero
      f i x hx
  refine ⟨h, v, ℓ, hne, ?_⟩
  dsimp only
  obtain ⟨φ, hleft, hderiv, _hright, _hrightDeriv, hpt, hcont⟩ :=
    SardScalarizedJetKernelParameterContDiffProbe.exists_implicitFunctionData_scalar_fixedDirections_kernelParameter_contDiffAt
      f i n x h v ℓ hf1 hfn hn hne
  have hdim := SardScalarDerivativeKernelDimensionDropProbe.finrank_ker_fderiv_scalar_fixedDirections_lt
    f i x h v ℓ hf1 hne
  let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x
  let G := (L : E →ₗ[ℝ] ℝ).ker
  letI hG : CompleteSpace G :=
    SardScalarizedJetImplicitFunctionDataProbe.kernelCompleteSpace L
  obtain ⟨V, hVopen, hVmem, hVreg⟩ :=
    @SardImplicitFunctionKernelParameterLocalRegularityProbe.ImplicitFunctionData.exists_open_kernelParameter_contDiffAt_and_differentiableAt
      E G inferInstance inferInstance inferInstance inferInstance inferInstance hG
      φ n hnTop hn hcont
  exact ⟨φ, hleft, hderiv, hpt, hdim, hcont, V, hVopen, hVmem, hVreg⟩

#print axioms exists_scalarizedJet_openRegularityData
end SardFirstNonzeroJetOpenRegularityDataProbe
