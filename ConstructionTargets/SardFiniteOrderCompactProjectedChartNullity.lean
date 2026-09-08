import ConstructionTargets.SardFiniteOrderProjectedChartSliceCertificates
import ConstructionTargets.SardCompactCoordinateFiberImageNullity
import ConstructionTargets.SardProjectedChartTargetFiberSliceContainment

open Set MeasureTheory

namespace SardFiniteOrderCompactProjectedChartNullityProbe

/-- Nullity certificates for all residual inverse-chart slices imply nullity
of the image of a compact set contained in the chart source. -/
theorem measure_image_zero_of_compact_projectedChart_of_sliceCertificates
    {X Y C G S : Type*} [TopologicalSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S]
    (μY : Measure Y) (μC : Measure C) (μS : Measure S)
    [Measure.IsAddHaarMeasure μY] [Measure.IsAddHaarMeasure μC]
    [Measure.IsAddHaarMeasure μS]
    (chart : OpenPartialHomeomorph X (C × G)) (coord : Y ≃L[ℝ] C × S)
    (f : X → Y) (K : Set X) (hK : IsCompact K) (hKsource : K ⊆ chart.source)
    (hf : ContinuousOn f K)
    (hfirst : (fun x => (chart x).1) = fun x => (coord (f x)).1)
    (hslices : ∀ c, μS ((fun z : G => (coord (f (chart.symm (c, z)))).2) ''
      {z | (c, z) ∈ chart.target}) = 0) :
    μY (f '' K) = 0 := by
  apply SardCompactCoordinateFiberImageNullityProbe.measure_image_zero_of_compact_coordinate_fibers
    μY μC μS coord f K hK hf
  intro c
  apply measure_mono_null _ (hslices c)
  intro w hw
  rcases hw with ⟨x, ⟨hxK, hxc⟩, rfl⟩
  have hcontain := SardProjectedChartTargetFiberSliceContainmentProbe.targetFiber_subset_inverseChartSlice
    chart coord f K hKsource hfirst c
  apply hcontain
  exact ⟨f x, ⟨⟨x, hxK, rfl⟩, hxc⟩, rfl⟩

#print axioms measure_image_zero_of_compact_projectedChart_of_sliceCertificates

end SardFiniteOrderCompactProjectedChartNullityProbe
