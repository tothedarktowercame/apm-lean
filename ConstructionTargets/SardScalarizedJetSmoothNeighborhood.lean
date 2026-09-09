import ConstructionTargets.SardScalarizedJetKernelParameterContDiff
import ConstructionTargets.SardSmoothNeighborhoodImplicitChart

open scoped ContDiff
noncomputable section
namespace SardScalarizedJetSmoothNeighborhoodProbe
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_scalarized_jet_smooth_chart
    (f : E → F) (i : ℕ) (x h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ ∞ f)
    (hne : ℓ (iteratedFDeriv ℝ (i + 1) f x (Fin.cons h v)) ≠ 0) :
    let g := fun y => ℓ (iteratedFDeriv ℝ i f y v)
    let L := fderiv ℝ g x
    let G := (L : E →ₗ[ℝ] ℝ).ker
    letI hG : CompleteSpace G :=
      SardScalarizedJetImplicitFunctionDataProbe.kernelCompleteSpace L
    ∃ (φ : @ImplicitFunctionData ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG) (e : OpenPartialHomeomorph E (ℝ × G)),
      (@ImplicitFunctionData.leftFun ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = g ∧ (@ImplicitFunctionData.leftDeriv ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = L ∧
      (@ImplicitFunctionData.rightFun ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = (fun y => G.orthogonalProjection y) ∧
      (@ImplicitFunctionData.rightDeriv ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = G.orthogonalProjection ∧ (@ImplicitFunctionData.pt ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) = x ∧
      x ∈ e.source ∧ e.source ⊆ (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ).source ∧
      (e : E → ℝ × G) = (@ImplicitFunctionData.prodFun ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) ∧
      (∀ y ∈ e.target, e.symm y = (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ).symm y) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ r z, z ∈ {z | (r,z) ∈ e.target} →
        ContDiffAt ℝ ∞ (fun w : G => ℓ (f (e.symm (r,w)))) z) := by
  dsimp only
  let g := fun y => ℓ (iteratedFDeriv ℝ i f y v)
  let L := fderiv ℝ g x
  let G := (L : E →ₗ[ℝ] ℝ).ker
  letI hG : CompleteSpace G :=
    SardScalarizedJetImplicitFunctionDataProbe.kernelCompleteSpace L
  have hf1 : ContDiff ℝ (i + 1) f := hf.of_le (by exact_mod_cast (show (i + 1 : ℕ∞) ≤ ⊤ from le_top))
  have hs : HasStrictFDerivAt g L x :=
    SardScalarizedJetStrictDerivativeProbe.hasStrictFDerivAt_scalar_fixedDirections_iteratedFDeriv
      f i x v ℓ hf1
  have hLh : L h ≠ 0 := by
    rw [SardNonzeroJetScalarDerivativeProbe.fderiv_scalar_fixedDirections_iteratedFDeriv_apply
      f i x h v ℓ hf1]
    exact hne
  obtain ⟨φ, hl, hd, hr, hrd, hp⟩ :=
    SardScalarImplicitFunctionDataDefiningFieldsProbe.exists_implicitFunctionData_with_defining_fields
      g x L hs hLh
  change @ImplicitFunctionData ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG at φ
  have hg : ContDiff ℝ ∞ g :=
    SardScalarizedJetRemainingOrderContDiffProbe.contDiff_scalar_fixedDirections_iteratedFDeriv_remainingOrder
      f i ∞ v ℓ (by simpa using hf)
  letI : CompleteSpace ((L : E →ₗ[ℝ] ℝ).ker) := hG
  have hleft : ContDiffOn ℝ ∞ (@ImplicitFunctionData.leftFun ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ).source := by
    rw [hl]; exact hg.contDiffOn
  have hright : ContDiffOn ℝ ∞ (@ImplicitFunctionData.rightFun ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ).source := by
    rw [hr]; exact G.orthogonalProjection.contDiff.contDiffOn
  obtain ⟨e, he, _, hsource, hforward, hinverse, hsm, hsi⟩ :=
    @SardSmoothNeighborhoodImplicitChartProbe.exists_smooth_implicit_chart
      E ℝ G inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance hG φ (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ).source (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ).open_source
      (@ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source ℝ inferInstance E inferInstance inferInstance inferInstance ℝ inferInstance inferInstance inferInstance G inferInstance inferInstance hG φ) (fun _ hz => hz) hleft hright
  have hex : x ∈ e.source := by simpa only [hp] using he
  refine ⟨φ, e, hl, hd, hr, hrd, hp, hex, hsource, hforward, hinverse, hsm, hsi, ?_⟩
  exact SardProjectedChartResidualSlicesContDiffOnProbe.contDiffAt_residual_inverseSlices_of_contDiffOn
    e f ℓ ∞ hsi hf.contDiffOn

#print axioms exists_scalarized_jet_smooth_chart
end SardScalarizedJetSmoothNeighborhoodProbe
