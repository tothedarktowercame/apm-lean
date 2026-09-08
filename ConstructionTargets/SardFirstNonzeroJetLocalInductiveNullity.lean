import ConstructionTargets.SardFirstNonzeroJetKernelParameterContainment
import ConstructionTargets.SardImplicitFunctionRestrictedKernelParameterization
import ConstructionTargets.SardLowerDimensionalLocalCriticalImageInduction

open Set MeasureTheory

noncomputable section
namespace SardFirstNonzeroJetLocalInductiveNullityProbe

/-- A restricted implicit-function kernel chart and the lower-dimensional Sard
hypothesis give nullity of one local piece of a first-nonzero-jet locus. -/
theorem firstNonzeroJetLocus_local_image_null
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
    (V : Set G) (hdim : Module.finrank ℝ G < Module.finrank ℝ E)
    (hn : n ≠ 0)
    (hf : ∀ z ∈ {z | (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target} ∩ V,
      ContDiffAt ℝ n f
        (φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)))
    (hg : ∀ z ∈ {z | (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target} ∩ V,
      ContDiffAt ℝ n
        (fun w : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, w)) z)
    (hKcrit : ∀ y ∈ K, ¬ Function.Surjective (fderiv ℝ f y)) :
    μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
      f K (i + 1) ∩
      (φ.toOpenPartialHomeomorph.source ∩
        φ.toOpenPartialHomeomorph ⁻¹' (Set.univ ×ˢ V)))) = 0 := by
  let g : G → E := fun z => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)
  let s : Set G := {z | (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target} ∩ V
  let t : Set E := SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
    f K (i + 1) ∩
    (φ.toOpenPartialHomeomorph.source ∩
      φ.toOpenPartialHomeomorph ⁻¹' (Set.univ ×ˢ V))
  apply SardLowerDimensionalLocalCriticalImageInductionProbe.localizedCriticalImage_null_of_lowerDim_parameterization
    μ n hind f g s t hdim hn
  · intro y hy
    rw [SardImplicitFunctionRestrictedKernelParameterizationProbe.ImplicitFunctionData.image_restricted_kernelParameter_eq]
    refine ⟨hy.2, ?_⟩
    rw [hleft, hpt]
    have hy0 := SardFirstNonzeroJetKernelParameterContainmentProbe.firstNonzeroJetLocus_succ_subset_scalarized_level_zero
      f K i hi v ℓ hy.1
    have hx0 := SardFirstNonzeroJetKernelParameterContainmentProbe.firstNonzeroJetLocus_succ_subset_scalarized_level_zero
      f K i hi v ℓ hx
    exact hy0.trans hx0.symm
  · exact hf
  · exact hg
  · intro y hy
    exact hKcrit y hy.1.1

#print axioms firstNonzeroJetLocus_local_image_null
end SardFirstNonzeroJetLocalInductiveNullityProbe
