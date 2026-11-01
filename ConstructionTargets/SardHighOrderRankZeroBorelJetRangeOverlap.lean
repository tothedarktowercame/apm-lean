import ConstructionTargets.SardHighOrderCompactRankZeroBorelJetRangeOverlap
import ConstructionTargets.SardClosedOpenImageNullity
import ConstructionTargets.SardDerivativeRankUpperLocusClosed

open Set MeasureTheory SardFirstNonzeroJetLocusDecompositionProbe
universe u v

theorem highOrder_rankZero_image_zero_of_borel_jet_range_overlap_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (k : ℕ)
    (hf : ContDiff ℝ (k + 2) f)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hind : ∀ e < Module.finrank ℝ E,
      SardHighOrderPredicateProbe.HighOrderNullityAtDimension.{u,v} e)
    (hT : SardHighOrderPredicateProbe.sardHighOrderThreshold (Module.finrank ℝ E) ≤ k + 2)
    (hoverlap : Module.finrank ℝ E + (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤
      Module.finrank ℝ F + (k + 2) + 1) :
    μ (f '' rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) = 0 := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast; omega)
  have hs : IsClosed (rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) := by
    simpa [rankStratum, Nat.le_zero] using
      SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost f 0 hf1
  have hnull := SardClosedOpenImageNullityProbe.measure_image_zero_of_closed_inter_open
    μ f (rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) univ hs isOpen_univ
    (fun K hK hsub => highOrder_compact_rankZero_image_zero_of_borel_jet_range_overlap
      μ f K hK k hf hadm (fun x hx => (hsub hx).1) hind hT hoverlap)
  simpa using hnull

#print axioms highOrder_rankZero_image_zero_of_borel_jet_range_overlap_induction
