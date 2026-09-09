import ConstructionTargets.SardCompactRankZeroThirdJetAssembly
import ConstructionTargets.SardJetClassicalAdmissibleLossNullity

open Set MeasureTheory SardFirstNonzeroJetLocusDecompositionProbe
universe u v

theorem compact_rankZero_image_zero_of_double_uncovered_jets
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (K : Set E) (hK : IsCompact K) (k : ℕ)
    (hf : ContDiff ℝ (k + 2) f)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hzero : K ⊆ rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0)
    (hind : ∀ e < Module.finrank ℝ E,
      SardClassicalFiniteOrderCriticalNullityPredicateProbe.ClassicalCriticalNullityAtDimension.{u,v} e)
    (huncovered : ∀ j ∈ Set.Icc 3 (k + 2),
      j * Module.finrank ℝ F ≤ Module.finrank ℝ E - 1 →
      Module.finrank ℝ F + (k + 2) < Module.finrank ℝ E + (j - 1) →
      μ (f '' firstNonzeroJetLocus f K j) = 0) :
    μ (f '' K) = 0 := by
  apply compact_rankZero_image_zero_of_uncovered_third_and_higherJets μ f K hK k hf hadm hzero hind
  intro j hj hdim
  by_cases hbudget : Module.finrank ℝ E + (j - 1) ≤ Module.finrank ℝ F + (k + 2)
  · have hcrit : ∀ x ∈ K, ¬ Function.Surjective (fderiv ℝ f x) := by
      intro x hx hsurj
      have hrange : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊤ :=
        LinearMap.range_eq_top.mpr hsurj
      have hz : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = 0 := hzero hx
      rw [hrange, finrank_top] at hz
      have hp := Module.finrank_pos (R := ℝ) (M := F)
      omega
    have hnull := firstNonzeroJet_image_null_of_classical_admissible_loss μ f K (k + 1)
      (j - 1) (by have := hj.1; omega) (by have := hj.2; omega) hf hbudget hind hcrit
    have hjpred : j - 1 + 1 = j := by have := hj.1; omega
    simpa only [hjpred] using hnull
  · exact huncovered j hj hdim (by omega)

#print axioms compact_rankZero_image_zero_of_double_uncovered_jets
