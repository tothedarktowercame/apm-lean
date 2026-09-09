import ConstructionTargets.SardScalarizedJetSmoothNeighborhood
import ConstructionTargets.SardFirstNonzeroJetKernelParameterContainment
import ConstructionTargets.SardScalarDerivativeKernelDimensionDrop
import ConstructionTargets.SardLowerDimensionalLocalCriticalImageInduction

open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace SardSmoothFirstNonzeroJetLocalInductionProbe
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]

theorem exists_local_firstNonzeroJet_image_null
    (μ : Measure F) (f : E → F) (K : Set E) (i : ℕ) (hi : 1 ≤ i)
    (x h : E) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ)
    (hf : ContDiff ℝ ∞ f)
    (hx : x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i+1))
    (hne : ℓ (iteratedFDeriv ℝ (i+1) f x (Fin.cons h v)) ≠ 0)
    (hKcrit : ∀ y ∈ K, ¬ Function.Surjective (fderiv ℝ f y)) :
    let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x
    let G := (L : E →ₗ[ℝ] ℝ).ker
    (Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (q : G → F) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ ∞ q z) →
        μ (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) →
    ∃ e : OpenPartialHomeomorph E (ℝ × G),
      x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i+1) ∩ e.source ∧
      Module.finrank ℝ G < Module.finrank ℝ E ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i+1) ∩ e.source ⊆
        (fun z : G => e.symm (0,z)) '' {z | (0,z) ∈ e.target}) ∧
      μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i+1) ∩ e.source)) = 0 := by
  dsimp only
  let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y v)) x
  let G := (L : E →ₗ[ℝ] ℝ).ker
  letI hG : CompleteSpace G := SardScalarizedJetImplicitFunctionDataProbe.kernelCompleteSpace L
  intro hind
  obtain ⟨φ, e, hl, _, _, _, _, he, _, hforward, _, hsm, hinv, _⟩ :=
    SardScalarizedJetSmoothNeighborhoodProbe.exists_scalarized_jet_smooth_chart f i x h v ℓ hf hne
  have hdim : Module.finrank ℝ G < Module.finrank ℝ E :=
    SardScalarDerivativeKernelDimensionDropProbe.finrank_ker_fderiv_scalar_fixedDirections_lt
      f i x h v ℓ (hf.of_le (by exact_mod_cast (show (i+1 : ℕ∞) ≤ ⊤ from le_top))) hne
  have hparam : SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i+1) ∩ e.source ⊆
      (fun z : G => e.symm (0,z)) '' {z | (0,z) ∈ e.target} := by
    rintro y ⟨hy, hys⟩
    have hz : (e y).1 = 0 := by
      rw [hforward]
      exact (congrFun hl y).trans
        (SardFirstNonzeroJetKernelParameterContainmentProbe.firstNonzeroJetLocus_succ_subset_scalarized_level_zero
          f K i hi v ℓ hy)
    have hp : (0, (e y).2) = e y := by ext <;> simp [hz]
    refine ⟨(e y).2, ?_, ?_⟩
    · change (0, (e y).2) ∈ e.target
      rw [hp]
      exact e.map_source hys
    · change e.symm (0, (e y).2) = y
      rw [hp]
      exact e.left_inv hys
  refine ⟨e, ⟨hx, he⟩, hdim, hsm, hinv, hparam, ?_⟩
  apply SardLowerDimensionalLocalCriticalImageInductionProbe.localizedCriticalImage_null_of_lowerDim_parameterization
    μ ∞ hind f (fun z : G => e.symm (0,z)) {z | (0,z) ∈ e.target}
      (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i+1) ∩ e.source)
      hdim (by simp) hparam
  · intro z hz
    exact hf.contDiffAt
  · intro z hz
    exact SardProjectedChartInverseSliceContDiffOnProbe.contDiffAt_inverseSlice_of_contDiffOn_symm
      e ∞ hinv 0 z hz
  · intro y hy
    exact hKcrit y hy.1.1

#print axioms exists_local_firstNonzeroJet_image_null
end SardSmoothFirstNonzeroJetLocalInductionProbe
