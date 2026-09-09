import ConstructionTargets.SardFirstNonzeroJetKernelTaylorNullity
import ConstructionTargets.SardImplicitFunctionRestrictedKernelParameterization

open Set MeasureTheory
open SardFirstNonzeroJetLocusDecompositionProbe
open SardImplicitFunctionRestrictedKernelParameterizationProbe
open SardImplicitFunctionKernelParameterLocalRegularityProbe

theorem exists_open_firstNonzeroJet_image_null_of_kernel_taylor_surplus
    {G E F : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [Nontrivial G] [MeasurableSpace G] [BorelSpace G]
    [ProperSpace G] [SecondCountableTopology G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (φ : ImplicitFunctionData ℝ E ℝ G) (f : E → F) (K : Set E)
    (i : ℕ) (hi : 1 ≤ i) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ) (x : E)
    (hleft : φ.leftFun = fun y => ℓ (iteratedFDeriv ℝ i f y v))
    (hpt : φ.pt = x) (hx : x ∈ firstNonzeroJetLocus f K (i + 1))
    (hp : ContDiffAt ℝ 1
      (fun w : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, w))
      (φ.rightFun φ.pt))
    (hf : ContDiff ℝ (i + 1) f)
    (hdim : Module.finrank ℝ G < (i + 1) * Module.finrank ℝ F) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧
      μ (f '' (firstNonzeroJetLocus f K (i + 1) ∩ W)) = 0 := by
  obtain ⟨V, hV, hxV, hreg⟩ :=
    φ.exists_open_kernelParameter_contDiffAt_and_differentiableAt 1 (by simp) (by simp) hp
  let p : G → E := fun z => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)
  let U : Set G := {z | (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target}
  have hU : IsOpen U := φ.toOpenPartialHomeomorph.open_target.preimage
    (continuous_const.prodMk continuous_id)
  let W := φ.toOpenPartialHomeomorph.source ∩
    φ.toOpenPartialHomeomorph ⁻¹' (Set.univ ×ˢ V)
  refine ⟨W, φ.isOpen_source_restrict_right V hV, ?_, ?_⟩
  · simpa only [hpt] using φ.pt_mem_source_restrict_right V hxV
  have hnull := C1_parameterized_flat_locus_image_addHaar_eq_zero
    μ f p (U ∩ V) (hU.inter hV) i (fun z hz => (hreg z hz.2).1) hf hdim
  apply measure_mono_null (t := (f ∘ p) '' {a ∈ U ∩ V | ∀ j, 1 ≤ j → j ≤ i →
    iteratedFDeriv ℝ j f (p a) = 0}) ?_ hnull
  rintro _ ⟨y, hy, rfl⟩
  have hlevel : φ.leftFun y = φ.leftFun φ.pt := by
    rw [hleft, hpt]
    have hy0 := SardFirstNonzeroJetKernelParameterContainmentProbe.firstNonzeroJetLocus_succ_subset_scalarized_level_zero
      f K i hi v ℓ hy.1
    have hx0 := SardFirstNonzeroJetKernelParameterContainmentProbe.firstNonzeroJetLocus_succ_subset_scalarized_level_zero
      f K i hi v ℓ hx
    exact hy0.trans hx0.symm
  have hyimg : y ∈ p '' (U ∩ V) := by
    rw [φ.image_restricted_kernelParameter_eq V]
    exact ⟨hy.2, hlevel⟩
  obtain ⟨z, hz, hzy⟩ := hyimg
  refine ⟨z, ⟨hz, ?_⟩, congrArg f hzy⟩
  intro j hj hji
  rw [hzy]
  exact hy.1.2.1 j hj (by omega)

#print axioms exists_open_firstNonzeroJet_image_null_of_kernel_taylor_surplus
