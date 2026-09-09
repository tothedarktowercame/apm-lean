import ConstructionTargets.SardFirstNonzeroJetTaylorSurplusNullity

open Set MeasureTheory SardFirstNonzeroJetLocusDecompositionProbe

theorem firstNonzeroJetLocus_image_null_of_taylor_surplus_all_source_dimensions
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (f : E → F) (K : Set E)
    (i : ℕ) (hi : 1 ≤ i) (hf : ContDiff ℝ (i + 1) f)
    (hdim : Module.finrank ℝ E - 1 < (i + 1) * Module.finrank ℝ F) :
    μ (f '' firstNonzeroJetLocus f K (i + 1)) = 0 := by
  by_cases hE : 1 < Module.finrank ℝ E
  · exact firstNonzeroJetLocus_image_null_of_taylor_surplus μ f K i hi hf hE hdim
  apply SardFirstNonzeroJetLocusLocalAggregationProbe.firstNonzeroJetLocus_image_null_of_locally_image_null
  intro x hx
  have hf' : ContDiff ℝ ((1 : WithTop ℕ∞) + i) f := by
    simpa [add_comm] using hf
  obtain ⟨h, v, ℓ, hne, φ, hleft, _hderiv, hpt, _hdrop, _hcont⟩ :=
    SardFirstNonzeroJetScalarizedChartDataProbe.exists_scalarizedJet_implicitFunctionData
      f i 1 x hf hf' (by simp) hx.2.2
  let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x
  let G := (L : E →ₗ[ℝ] ℝ).ker
  letI : CompleteSpace G := SardScalarizedJetImplicitFunctionDataProbe.kernelCompleteSpace L
  have hdimG : Module.finrank ℝ G + 1 = Module.finrank ℝ E :=
    SardScalarDerivativeKernelDimensionProbe.finrank_ker_fderiv_scalar_fixedDirections_add_one
      f i x h v ℓ hf hne
  letI : Subsingleton G := (Module.finrank_zero_iff (R := ℝ) (M := G)).mp (by omega)
  refine ⟨φ.toOpenPartialHomeomorph.source, φ.toOpenPartialHomeomorph.open_source, ?_, ?_⟩
  · simpa only [hpt] using φ.pt_mem_toOpenPartialHomeomorph_source
  have hsub := SardFirstNonzeroJetKernelParameterContainmentProbe.firstNonzeroJetLocus_inter_source_subset_image_kernelParameter
    φ f K i hi v ℓ x hleft hpt hx
  have hs : (firstNonzeroJetLocus f K (i + 1) ∩ φ.toOpenPartialHomeomorph.source).Subsingleton := by
    intro y hy z hz
    obtain ⟨a, _, ha⟩ := hsub hy
    obtain ⟨b, _, hb⟩ := hsub hz
    have hab : a = b := Subsingleton.elim a b
    rw [hab] at ha
    exact ha.symm.trans hb
  exact (hs.image f).measure_zero μ

#print axioms firstNonzeroJetLocus_image_null_of_taylor_surplus_all_source_dimensions
