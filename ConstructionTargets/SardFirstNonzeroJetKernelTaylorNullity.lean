import ConstructionTargets.SardC1ParameterizedFlatLocusNullity
import ConstructionTargets.SardFirstNonzeroJetKernelParameterContainment

open Set MeasureTheory
open SardFirstNonzeroJetLocusDecompositionProbe

theorem firstNonzeroJet_kernelChart_image_null_of_taylor_surplus
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
    (hp : ∀ z, (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target →
      ContDiffAt ℝ 1
        (fun w : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, w)) z)
    (hf : ContDiff ℝ (i + 1) f)
    (hdim : Module.finrank ℝ G < (i + 1) * Module.finrank ℝ F) :
    μ (f '' (firstNonzeroJetLocus f K (i + 1) ∩
      φ.toOpenPartialHomeomorph.source)) = 0 := by
  let p : G → E := fun z => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)
  let U : Set G := {z | (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target}
  have hU : IsOpen U := φ.toOpenPartialHomeomorph.open_target.preimage
    (continuous_const.prodMk continuous_id)
  have hnull := C1_parameterized_flat_locus_image_addHaar_eq_zero
    μ f p U hU i hp hf hdim
  apply measure_mono_null (t := (f ∘ p) '' {a ∈ U | ∀ j, 1 ≤ j → j ≤ i →
    iteratedFDeriv ℝ j f (p a) = 0}) ?_ hnull
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzy⟩ :=
    SardFirstNonzeroJetKernelParameterContainmentProbe.firstNonzeroJetLocus_inter_source_subset_image_kernelParameter
      φ f K i hi v ℓ x hleft hpt hx hy
  refine ⟨z, ⟨hz, ?_⟩, ?_⟩
  · intro j hj hji
    change p z = y at hzy
    rw [hzy]
    exact hy.1.2.1 j hj (by omega)
  · change f (p z) = f y
    exact congrArg f hzy

#print axioms firstNonzeroJet_kernelChart_image_null_of_taylor_surplus
