import ConstructionTargets.SardCompactTargetFiberProjectedSliceImageNullity
import ConstructionTargets.SardProjectedChartTargetFiberSliceContainment

open Set MeasureTheory

namespace SardCompactProjectedChartImageNullityProbe

/-- A compact set inside a projected chart has null image when all fixed-first-coordinate
inverse slices satisfy the lower-dimensional Sard hypotheses. -/
theorem measure_image_zero_of_compact_projectedChart
    {D Y G R C S X : Type*} [TopologicalSpace X]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S]
    (μY : Measure Y) (μC : Measure C) (μS : Measure S)
    [Measure.IsAddHaarMeasure μY] [Measure.IsAddHaarMeasure μC]
    [Measure.IsAddHaarMeasure μS]
    (n : WithTop ℕ∞)
    (hind : Module.finrank ℝ G < Module.finrank ℝ D →
      ∀ (q : G → S) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ n q z) →
        μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (chart : OpenPartialHomeomorph X (C × G)) (coord : Y ≃L[ℝ] C × S)
    (f : X → Y) (K : Set X) (hK : IsCompact K) (hKsource : K ⊆ chart.source)
    (hf : ContinuousOn f K)
    (hfirst : (fun x => (chart x).1) = fun x => (coord (f x)).1)
    (P : S →L[ℝ] R)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ D) (hn : n ≠ 0)
    (hq : ∀ r z, z ∈ {z | (r, z) ∈ chart.target} →
      ContDiffAt ℝ n (fun z : G => (coord (f (chart.symm (r, z)))).2) z)
    (hP : Function.Surjective P)
    (hzero : ∀ r z, z ∈ {z | (r, z) ∈ chart.target} →
      HasFDerivAt
        (P ∘ fun z : G => (coord (f (chart.symm (r, z)))).2)
        (0 : G →L[ℝ] R) z) :
    μY (f '' K) = 0 := by
  apply SardCompactTargetFiberProjectedSliceImageNullityProbe.measure_image_zero_of_compact_targetFiber_projectedSlices
    μY μC μS n hind coord f K hK hf
    (fun r z => (coord (f (chart.symm (r, z)))).2)
    (fun r => {z | (r, z) ∈ chart.target}) P
  · exact SardProjectedChartTargetFiberSliceContainmentProbe.targetFiber_subset_inverseChartSlice
      chart coord f K hKsource hfirst
  · exact hdim
  · exact hn
  · exact hq
  · exact hP
  · exact hzero

#print axioms measure_image_zero_of_compact_projectedChart

end SardCompactProjectedChartImageNullityProbe
