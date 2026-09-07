import ConstructionTargets.SardFirstNonzeroJetLocusDecomposition
import ConstructionTargets.SardImplicitFunctionLevelSetKernelParameterization

open Set

noncomputable section
namespace SardFirstNonzeroJetKernelParameterContainmentProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace E] in
/-- A first-nonzero `(i+1)`-jet locus lies in the zero level of every
scalarized fixed-direction `i`-jet. -/
theorem firstNonzeroJetLocus_succ_subset_scalarized_level_zero
    (f : E → F) (K : Set E) (i : ℕ) (hi : 1 ≤ i)
    (v : Fin i → E) (ℓ : F →L[ℝ] ℝ) :
    SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i + 1) ⊆
      {y | ℓ (iteratedFDeriv ℝ i f y v) = 0} := by
  intro y hy
  simpa using congrArg (fun A => ℓ (A v))
    (hy.2.1 i hi (Nat.lt_succ_self i))

/-- After identifying the implicit-function left coordinate with a scalarized
`i`-jet and its base point with a point of the first-nonzero `(i+1)`-jet locus,
the localized locus is contained in the exact inverse-chart kernel image. -/
theorem firstNonzeroJetLocus_inter_source_subset_image_kernelParameter
    (φ : ImplicitFunctionData ℝ E ℝ G) (f : E → F) (K : Set E)
    (i : ℕ) (hi : 1 ≤ i) (v : Fin i → E) (ℓ : F →L[ℝ] ℝ) (x : E)
    (hleft : φ.leftFun = fun y => ℓ (iteratedFDeriv ℝ i f y v))
    (hpt : φ.pt = x)
    (hx : x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
      f K (i + 1)) :
    SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i + 1) ∩
        φ.toOpenPartialHomeomorph.source ⊆
      (fun z : G => φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, z)) ''
        {z | (φ.leftFun φ.pt, z) ∈ φ.toOpenPartialHomeomorph.target} := by
  rw [SardImplicitFunctionLevelSetKernelParameterizationProbe.ImplicitFunctionData.image_kernelParam_eq_inter_source_leftFun_level]
  rintro y ⟨hy, hys⟩
  refine ⟨hys, ?_⟩
  rw [hleft, hpt]
  have hy0 := firstNonzeroJetLocus_succ_subset_scalarized_level_zero
    f K i hi v ℓ hy
  have hx0 := firstNonzeroJetLocus_succ_subset_scalarized_level_zero
    f K i hi v ℓ hx
  exact hy0.trans hx0.symm

#print axioms firstNonzeroJetLocus_succ_subset_scalarized_level_zero
#print axioms firstNonzeroJetLocus_inter_source_subset_image_kernelParameter
end SardFirstNonzeroJetKernelParameterContainmentProbe
