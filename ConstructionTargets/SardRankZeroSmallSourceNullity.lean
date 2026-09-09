import ConstructionTargets.SardCompactRankZeroSmallSourceNullity
import ConstructionTargets.SardClosedOpenImageNullity
import ConstructionTargets.SardDerivativeRankUpperLocusClosed

open Set MeasureTheory

theorem rankZero_image_zero_of_sourceDim_le_twice_targetDim
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (k : ℕ) (hf : ContDiff ℝ (k + 1) f)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 1))
    (hdim : Module.finrank ℝ E ≤ 2 * Module.finrank ℝ F) :
    μ (f '' rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) = 0 := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast; omega)
  have hs : IsClosed (rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) := by
    simpa [rankStratum, Nat.le_zero] using
      SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost f 0 hf1
  have hnull := SardClosedOpenImageNullityProbe.measure_image_zero_of_closed_inter_open
    μ f (rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) univ hs isOpen_univ
    (fun K hK hsub => compact_rankZero_image_zero_of_sourceDim_le_twice_targetDim
      μ f K hK k hf hadm (fun x hx => (hsub hx).1) hdim)
  simpa using hnull

#print axioms rankZero_image_zero_of_sourceDim_le_twice_targetDim
