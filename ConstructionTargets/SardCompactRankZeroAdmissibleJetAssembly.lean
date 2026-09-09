import ConstructionTargets.SardCompactFlatNonnegativeBudgetNullity
import ConstructionTargets.SardFiniteOrderTaylorBudgetEndpoint
import ConstructionTargets.SardFiniteOrderRankZeroFirstJetEmpty
import ConstructionTargets.SardFirstNonzeroJetFiniteAssembly

open Metric Set MeasureTheory
open scoped ENNReal NNReal

theorem compact_rankZero_image_zero_of_admissible_higherJets
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 1))
    (hzero : K ⊆ rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0)
    (hhigher : ∀ i ∈ Set.Icc 2 (k + 1),
      μF (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K i) = 0) :
    μF (f '' K) = 0 := by
  apply SardFirstNonzeroJetFiniteAssemblyProbe.image_null_of_flat_first_and_higher_firstNonzeroJetLoci
    μF f K (k + 1)
  · apply compact_flatThrough_image_zero_of_nonnegative_budget μF f K hK k hf
    rcases SardFiniteOrderTaylorBudgetEndpointProbe.taylorBudget_strict_or_endpoint
      (order := k + 1) (Module.finrank_pos (R := ℝ) (M := F)) (by omega) hadm with ⟨d, _, hd⟩ | heq
    · omega
    · omega
  · rw [SardFiniteOrderRankZeroFirstJetEmptyProbe.firstNonzeroJetLocus_one_eq_empty_of_rankZero
      f K hzero]
    simp
  · exact hhigher

#print axioms compact_rankZero_image_zero_of_admissible_higherJets
