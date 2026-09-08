import ConstructionTargets.SardExactRankClosedOpenProjectedChartNullity
import ConstructionTargets.SardProjectedSmoothChartTargetData
import ConstructionTargets.SardProjectedRangeKernelDimensionDrop
import ConstructionTargets.SardFirstNonzeroJetOneFDerivNonzero
import ConstructionTargets.SardDerivativeRankUpperLocusClosed

open Set MeasureTheory

noncomputable section

namespace SardFirstDerivativeRankPiecePointwiseClosedOpenNullityProbe

/-- At an order-one exact-rank point, the projected chart supplies an open
neighborhood on which the closed rank-upper locus has null image. -/
theorem exists_open_rankUpper_image_zero
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (K : Set E) (r : ℕ) (hf : ContDiff ℝ 1 f) (x : E)
    (hxjet : x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1)
    (hxrank : x ∈ rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)
    (hcrit : ¬ Function.Surjective (fderiv ℝ f x))
    (hind : ∀ (μS : Measure
        (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ),
      Measure.IsAddHaarMeasure μS →
      ∀ (q : ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
          (fderiv ℝ f x)).ker →
          (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ)
        (u : Set ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
          (fderiv ℝ f x)).ker),
        (∀ z ∈ u, ContDiffAt ℝ 1 q z) →
        μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      μF (f '' ({y | Module.finrank ℝ
        (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ U)) = 0 := by
  let L := fderiv ℝ f x
  have hstrict : HasStrictFDerivAt f L x :=
    hf.contDiffAt.hasStrictFDerivAt'
      (hf.differentiable one_ne_zero x).hasFDerivAt one_ne_zero
  obtain ⟨chart, hxsource, hfirst, hchart, hsymm, hsurj⟩ :=
    SardProjectedSmoothChartTargetDataProbe.exists_projected_smoothChart_target_data
      f x L hstrict hf.contDiffAt
  let A : Set E := {y | Module.finrank ℝ
    (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r}
  refine ⟨chart.source, chart.open_source, hxsource, ?_⟩
  apply SardExactRankClosedOpenProjectedChartNullityProbe.measure_image_zero_of_exactRank_closedOpen_projectedChart
    μF f hf L hcrit r hxrank
    hind chart A chart.source
    (SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost f r hf)
    chart.open_source (fun _ h => h)
  · simpa [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply] using hfirst
  · exact hsymm
  · intro y hy
    exact hsurj y hy (fderiv ℝ f y)
      (hf.differentiable one_ne_zero y).hasFDerivAt
  · intro y hy hylocus
    exact hylocus.1
  · exact SardProjectedRangeKernelDimensionDropProbe.finrank_ker_rangeProjection_comp_lt
      L (SardFirstNonzeroJetOneFDerivNonzeroProbe.fderiv_ne_zero_of_mem_firstNonzeroJetLocus_one
        f K x hxjet)

#print axioms exists_open_rankUpper_image_zero

end SardFirstDerivativeRankPiecePointwiseClosedOpenNullityProbe
