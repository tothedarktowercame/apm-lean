import ConstructionTargets.SardSmoothFirstNonzeroJetLocalInduction
import ConstructionTargets.SardFirstNonzeroJetLocusLocalAggregation
import ConstructionTargets.SardNonzeroSuccessorJetScalarDirections
import ConstructionTargets.SardCompactRankZeroAdmissibleJetAssembly

open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace SardSmoothCompactRankZeroInductionProbe
universe u v

theorem compact_rankZero_image_null_of_smooth_local_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K)
    (hf : ContDiff ℝ ∞ f) (hzero : ∀ y ∈ K, fderiv ℝ f y = 0)
    (hind : ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
      [FiniteDimensional ℝ G] [CompleteSpace G],
      Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (q : G → F) (s : Set G),
        (∀ z ∈ s, ContDiffAt ℝ ∞ q z) →
        μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) :
    μ (f '' K) = 0 := by
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
        ∀ (q : G → F) (s : Set G),
          (∀ z ∈ s, ContDiffAt ℝ ∞ q z) →
          μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0 :=
      @hind G inferInstance inferInstance inferInstance hG
    obtain ⟨e, he, _, _, _, _, hn⟩ :=
      SardSmoothFirstNonzeroJetLocalInductionProbe.exists_local_firstNonzeroJet_image_null
        μ f K i hi x h w ℓ hf hx hne hcrit hI
    exact ⟨e.source, e.open_source, he.2, hn⟩

#print axioms compact_rankZero_image_null_of_smooth_local_induction
end SardSmoothCompactRankZeroInductionProbe
