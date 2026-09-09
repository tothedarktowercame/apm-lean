import ConstructionTargets.SardCompactRankZeroUncoveredJetAssembly
import ConstructionTargets.SardClosedOpenImageNullity
import ConstructionTargets.SardDerivativeRankUpperLocusClosed

open Set MeasureTheory SardFirstNonzeroJetLocusDecompositionProbe

theorem rankZero_inter_open_image_zero_of_uncovered_higherJets
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (U : Set E) (hU : IsOpen U) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 1))
    (huncovered : ∀ j ∈ Set.Icc 2 (k + 1),
      j * Module.finrank ℝ F ≤ Module.finrank ℝ E - 1 →
      μ (f '' firstNonzeroJetLocus f U j) = 0) :
    μ (f '' (rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0 ∩ U)) = 0 := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast; omega)
  have hs : IsClosed (rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) := by
    simpa [rankStratum, Nat.le_zero] using
      SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost f 0 hf1
  apply SardClosedOpenImageNullityProbe.measure_image_zero_of_closed_inter_open
    μ f _ U hs hU
  intro K hK hsub
  apply compact_rankZero_image_zero_of_uncovered_higherJets μ f K hK k hf hadm
    (fun x hx => (hsub hx).1)
  intro j hj hdim
  apply measure_mono_null (Set.image_mono ?_) (huncovered j hj hdim)
  intro x hx
  exact ⟨(hsub hx.1).2, hx.2⟩

#print axioms rankZero_inter_open_image_zero_of_uncovered_higherJets
