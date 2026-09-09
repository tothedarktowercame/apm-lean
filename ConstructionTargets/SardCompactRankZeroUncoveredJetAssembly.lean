import ConstructionTargets.SardCompactRankZeroAdmissibleJetAssembly
import ConstructionTargets.SardFirstNonzeroJetAllSourceTaylorNullity

open Set MeasureTheory SardFirstNonzeroJetLocusDecompositionProbe

theorem compact_rankZero_image_zero_of_uncovered_higherJets
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 1))
    (hzero : K ⊆ rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0)
    (huncovered : ∀ j ∈ Set.Icc 2 (k + 1),
      j * Module.finrank ℝ F ≤ Module.finrank ℝ E - 1 →
      μ (f '' firstNonzeroJetLocus f K j) = 0) :
    μ (f '' K) = 0 := by
  apply compact_rankZero_image_zero_of_admissible_higherJets μ f K hK k hf hadm hzero
  intro j hj
  by_cases hdim : Module.finrank ℝ E - 1 < j * Module.finrank ℝ F
  · have hj1 : j - 1 + 1 = j := by have := hj.1; omega
    have hfj : ContDiff ℝ ((j - 1 : ℕ) + 1) f := hf.of_le (by
      exact_mod_cast (show j - 1 + 1 ≤ k + 1 by have := hj.2; omega))
    have hnull := firstNonzeroJetLocus_image_null_of_taylor_surplus_all_source_dimensions
      μ f K (j - 1) (by have := hj.1; omega) hfj (by simpa only [hj1] using hdim)
    simpa only [hj1] using hnull
  · exact huncovered j hj (by omega)

#print axioms compact_rankZero_image_zero_of_uncovered_higherJets
