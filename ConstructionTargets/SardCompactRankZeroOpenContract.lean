import ConstructionTargets.SardScalarizedJetSmoothNeighborhood
import ConstructionTargets.SardFirstNonzeroJetKernelParameterContainment
import ConstructionTargets.SardScalarDerivativeKernelDimensionDrop
import ConstructionTargets.SardLowerDimensionalLocalCriticalImageInduction
import ConstructionTargets.SardFirstNonzeroJetLocusLocalAggregation
import ConstructionTargets.SardNonzeroSuccessorJetScalarDirections
import ConstructionTargets.SardCompactRankZeroAdmissibleJetAssembly
import ConstructionTargets.SardPositiveRankSliceOpenInductionContract

open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace SardOpenContractFirstJetProbe
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
      ∀ (q : G → F) (U u : Set G),
        IsOpen U → u ⊆ U → ContDiffOn ℝ ∞ q U →
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
  let U : Set G := {z | (0,z) ∈ e.target}
  let g : G → E := fun z => e.symm (0,z)
  have hU : IsOpen U := e.open_target.preimage (by fun_prop)
  have hg : ∀ z ∈ U, ContDiffAt ℝ ∞ g z := by
    intro z hz
    exact SardProjectedChartInverseSliceContDiffOnProbe.contDiffAt_inverseSlice_of_contDiffOn_symm
      e ∞ hinv 0 z hz
  have hgOn : ContDiffOn ℝ ∞ g U := fun z hz => (hg z hz).contDiffWithinAt
  have hq : ContDiffOn ℝ ∞ (f ∘ g) U :=
    hf.contDiffOn.comp hgOn (fun _ _ => Set.mem_univ _)
  apply SardParameterizedLocalCriticalImageNullityProbe.localizedCriticalImage_null_of_parameterized_on
    μ f g U (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i+1) ∩ e.source)
    hparam
  · intro z hz
    exact hf.differentiable (by simp) (g z)
  · intro z hz
    exact (hg z hz).differentiableAt (by simp)
  · intro y hy
    exact hKcrit y hy.1.1
  · exact hind hdim (f ∘ g) U U hU (Subset.refl _) hq

#print axioms exists_local_firstNonzeroJet_image_null
end SardOpenContractFirstJetProbe


open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace SardCompactRankZeroOpenContractProbe
universe u v

theorem compact_rankZero_image_null_of_smooth_local_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K)
    (hf : ContDiff ℝ ∞ f) (hzero : ∀ y ∈ K, fderiv ℝ f y = 0)
    (hind : ∀ (G : Type u) [NormedAddCommGroup G] [InnerProductSpace ℝ G]
      [FiniteDimensional ℝ G] [CompleteSpace G],
      Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (q : G → F) (U s : Set G),
        IsOpen U → s ⊆ U → ContDiffOn ℝ ∞ q U →
        μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) :
    μ (f '' K) = 0 := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hcrit : ∀ y ∈ K, ¬ Function.Surjective (fderiv ℝ f y) := by
    intro y hy hs
    obtain ⟨a, ha⟩ := exists_ne (0 : F)
    obtain ⟨b, hb⟩ := hs a
    rw [hzero y hy] at hb
    exact ha (by simpa using hb.symm)
  apply compact_rankZero_image_zero_of_admissible_higherJets μ f K hK (Module.finrank ℝ E)
  · exact hf.of_le (by exact_mod_cast (show (Module.finrank ℝ E + 1 : ℕ∞) ≤ ⊤ from le_top))
  · unfold SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
    omega
  · intro y hy
    change Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) = 0
    rw [hzero y hy]
    simp
  · intro j hj
    rcases hj with ⟨hjlo, hjhi⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hi : 1 ≤ i := by omega
    apply SardFirstNonzeroJetLocusLocalAggregationProbe.firstNonzeroJetLocus_image_null_of_locally_image_null
    intro x hx
    obtain ⟨h, w, ℓ, hne⟩ :=
      SardNonzeroSuccessorJetScalarDirectionsProbe.exists_firstDirection_tail_scalar_apply_ne_zero
        f i x hx.2.2
    let L := fderiv ℝ (fun y => ℓ (iteratedFDeriv ℝ i f y w)) x
    let G := (L : E →ₗ[ℝ] ℝ).ker
    letI hG : CompleteSpace G := SardScalarizedJetImplicitFunctionDataProbe.kernelCompleteSpace L
    have hI : Module.finrank ℝ G < Module.finrank ℝ E →
        ∀ (q : G → F) (U s : Set G),
          IsOpen U → s ⊆ U → ContDiffOn ℝ ∞ q U →
          μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0 :=
      @hind G inferInstance inferInstance inferInstance hG
    obtain ⟨e, he, _, _, _, _, hn⟩ :=
      SardOpenContractFirstJetProbe.exists_local_firstNonzeroJet_image_null
        μ f K i hi x h w ℓ hf hx hne hcrit hI
    exact ⟨e.source, e.open_source, he.2, hn⟩

#print axioms compact_rankZero_image_null_of_smooth_local_induction
theorem compact_rankZero_image_null_of_global_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K)
    (hf : ContDiff ℝ ∞ f) (hzero : ∀ y ∈ K, fderiv ℝ f y = 0)
    (hind : ∀ (G : Type u) [NormedAddCommGroup G] [InnerProductSpace ℝ G]
      [FiniteDimensional ℝ G] [CompleteSpace G],
      Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ q : G → F, ContDiff ℝ ∞ q →
        μ (q '' {z | ¬ Function.Surjective (fderiv ℝ q z)}) = 0) :
    μ (f '' K) = 0 := by
  exact compact_rankZero_image_null_of_smooth_local_induction μ f K hK hf hzero
    (SardPositiveRankSliceOpenInductionContractProbe.open_induction_of_global (E := E) μ hind)
#print axioms compact_rankZero_image_null_of_global_induction
end SardCompactRankZeroOpenContractProbe
