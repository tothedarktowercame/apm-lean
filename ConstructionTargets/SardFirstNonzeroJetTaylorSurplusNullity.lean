import ConstructionTargets.SardFirstNonzeroJetLocalKernelTaylorNullity
import ConstructionTargets.SardFirstNonzeroJetScalarizedChartData
import ConstructionTargets.SardFirstNonzeroJetLocusLocalAggregation

open Set MeasureTheory SardFirstNonzeroJetLocusDecompositionProbe

theorem firstNonzeroJetLocus_image_null_of_taylor_surplus
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (f : E → F) (K : Set E)
    (i : ℕ) (hi : 1 ≤ i) (hf : ContDiff ℝ (i + 1) f)
    (hE : 1 < Module.finrank ℝ E)
    (hdim : Module.finrank ℝ E - 1 < (i + 1) * Module.finrank ℝ F) :
    μ (f '' firstNonzeroJetLocus f K (i + 1)) = 0 := by
  apply SardFirstNonzeroJetLocusLocalAggregationProbe.firstNonzeroJetLocus_image_null_of_locally_image_null
  intro x hx
  have hf' : ContDiff ℝ ((1 : WithTop ℕ∞) + i) f := by
    simpa [add_comm] using hf
  obtain ⟨h, v, ℓ, hne, φ, hleft, _hderiv, hpt, _hdrop, hcont⟩ :=
    SardFirstNonzeroJetScalarizedChartDataProbe.exists_scalarizedJet_implicitFunctionData
      f i 1 x hf hf' (by simp) hx.2.2
  let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x
  let G := (L : E →ₗ[ℝ] ℝ).ker
  letI : CompleteSpace G := SardScalarizedJetImplicitFunctionDataProbe.kernelCompleteSpace L
  letI hSC : SecondCountableTopology G := inferInstance
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  have hdimG : Module.finrank ℝ G + 1 = Module.finrank ℝ E :=
    SardScalarDerivativeKernelDimensionProbe.finrank_ker_fderiv_scalar_fixedDirections_add_one
      f i x h v ℓ hf hne
  letI : Nontrivial G := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  exact @exists_open_firstNonzeroJet_image_null_of_kernel_taylor_surplus
    G E F inferInstance inferInstance inferInstance inferInstance
    (borel G) ⟨rfl⟩ inferInstance hSC
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    μ inferInstance φ f K i hi v ℓ x hleft hpt hx hcont hf (by omega)

#print axioms firstNonzeroJetLocus_image_null_of_taylor_surplus
