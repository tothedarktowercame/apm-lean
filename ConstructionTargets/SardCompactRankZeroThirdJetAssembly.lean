import ConstructionTargets.SardCompactRankZeroUncoveredJetAssembly
import ConstructionTargets.SardSecondJetClassicalInductionNullity

open Set MeasureTheory SardFirstNonzeroJetLocusDecompositionProbe
universe u v

theorem compact_rankZero_image_zero_of_uncovered_third_and_higherJets
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
      μ (f '' firstNonzeroJetLocus f K j) = 0) :
    μ (f '' K) = 0 := by
  apply compact_rankZero_image_zero_of_uncovered_higherJets μ f K hK (k + 1) hf hadm hzero
  intro j hj hdim
  by_cases hj2 : j = 2
  · subst j
    apply secondJet_image_null_of_classical_lowerDimension_induction μ f K k hf hadm hind
    intro x hx hsurj
    have hrange : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hz : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = 0 := hzero hx
    rw [hrange, finrank_top] at hz
    have hp := Module.finrank_pos (R := ℝ) (M := F)
    omega
  · exact huncovered j ⟨by have := hj.1; omega, hj.2⟩ hdim

#print axioms compact_rankZero_image_zero_of_uncovered_third_and_higherJets
