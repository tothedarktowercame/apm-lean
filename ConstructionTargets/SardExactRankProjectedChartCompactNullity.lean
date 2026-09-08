import ConstructionTargets.SardDerivativeRangeOrthogonalCompactChartNullity
import ConstructionTargets.SardProjectedChartOrthogonalResidualSliceZero
import ConstructionTargets.SardProjectedChartOrthogonalResidualNullityData

open Set MeasureTheory

noncomputable section

namespace SardExactRankProjectedChartCompactNullityProbe

/-- Exact-rank projected-chart data supplies the bundled orthogonal slice
hypotheses and hence compact image nullity. -/
theorem measure_image_zero_of_exactRank_projectedChart
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (L : E →L[ℝ] F) (hL : ¬ Function.Surjective L) (r : ℕ)
    (hind : ∀ (μS : Measure (LinearMap.range L.toLinearMap)ᗮ),
      Measure.IsAddHaarMeasure μS →
      ∀ (q : G → (LinearMap.range L.toLinearMap)ᗮ) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ 1 q z) →
        μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (chart : OpenPartialHomeomorph E ((LinearMap.range L.toLinearMap) × G))
    (K : Set E) (hK : IsCompact K) (hKsource : K ⊆ chart.source)
    (hfK : ContinuousOn f K)
    (hfirst : (fun x => (chart x).1) =
      fun x => (LinearMap.range L.toLinearMap).orthogonalProjection (f x))
    (hsymm : ContDiffOn ℝ 1 chart.symm chart.target)
    (hf : ContDiffOn ℝ 1 f chart.source)
    (hbase : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hrank : ∀ x ∈ chart.source,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r)
    (hsurj : ∀ x ∈ chart.source,
      ((LinearMap.range L.toLinearMap).orthogonalProjection.comp
        (fderiv ℝ f x)).range = ⊤)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ E) :
    μF (f '' K) = 0 := by
  have hzero :=
    SardProjectedChartOrthogonalResidualSliceZeroProbe.forall_hasFDerivAt_zero_orthogonalResidual_inverseSlice
      f L r chart hfirst hsymm hf hbase hrank hsurj
  have hdata :=
    SardProjectedChartOrthogonalResidualNullityDataProbe.orthogonalResidual_inverseSlice_nullity_data
      L chart f hsymm hf hzero
  apply SardDerivativeRangeOrthogonalCompactChartNullityProbe.measure_image_zero_of_rangeOrthogonal_compactChart
    μF L hL hind chart f K hK hKsource hfK
  · funext x
    rw [congrFun hfirst x]
    exact (congrArg Prod.fst
      (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply
        (LinearMap.range L.toLinearMap) (f x))).symm
  · exact hdim
  · exact hdata

#print axioms measure_image_zero_of_exactRank_projectedChart

end SardExactRankProjectedChartCompactNullityProbe
