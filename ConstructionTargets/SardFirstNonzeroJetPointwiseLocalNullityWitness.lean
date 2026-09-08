import ConstructionTargets.SardFirstNonzeroJetLocalInductiveNullity
import ConstructionTargets.SardFirstNonzeroJetLocusLocalAggregation
import ConstructionTargets.SardImplicitFunctionRestrictedKernelParameterization

open Set MeasureTheory

noncomputable section
namespace SardFirstNonzeroJetPointwiseLocalNullityWitnessProbe

/-- One exact restricted implicit chart supplies the existential open local-nullity
witness consumed by refined-locus aggregation. -/
theorem exists_open_firstNonzeroJetLocus_local_image_null
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [CompleteSpace G]
    (μ : Measure F) (n : WithTop ℕ∞)
    (hind : Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (q : G → F) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ n q z) →
        μ (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (φ : ImplicitFunctionData ℝ E ℝ G) (f : E → F) (K : Set E)
    (i : ℕ) (hi : 1 ≤ i) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ) (x : E)
    (hleft : φ.leftFun = fun y => ℓ (iteratedFDeriv ℝ i f y v))
    (hpt : φ.pt = x)
    (hx : x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i + 1))
    (V : Set G) (hVopen : IsOpen V) (hVmem : φ.rightFun φ.pt ∈ V)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ E) (hn : n ≠ 0)
    (hf : ∀ z ∈ {z | (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target} ∩ V,
      ContDiffAt ℝ n f (φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)))
    (hg : ∀ z ∈ {z | (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target} ∩ V,
      ContDiffAt ℝ n
        (fun w : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, w)) z)
    (hKcrit : ∀ y ∈ K, ¬ Function.Surjective (fderiv ℝ f y)) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
        f K (i + 1) ∩ U)) = 0 := by
  let U := φ.toOpenPartialHomeomorph.source ∩
    φ.toOpenPartialHomeomorph ⁻¹' (Set.univ ×ˢ V)
  refine ⟨U, ?_, ?_, ?_⟩
  · exact SardImplicitFunctionRestrictedKernelParameterizationProbe.ImplicitFunctionData.isOpen_source_restrict_right
      φ V hVopen
  · rw [← hpt]
    exact SardImplicitFunctionRestrictedKernelParameterizationProbe.ImplicitFunctionData.pt_mem_source_restrict_right
      φ V hVmem
  · exact SardFirstNonzeroJetLocalInductiveNullityProbe.firstNonzeroJetLocus_local_image_null
      μ n hind φ f K i hi v ℓ x hleft hpt hx V hdim hn hf hg hKcrit

#print axioms exists_open_firstNonzeroJetLocus_local_image_null
end SardFirstNonzeroJetPointwiseLocalNullityWitnessProbe
