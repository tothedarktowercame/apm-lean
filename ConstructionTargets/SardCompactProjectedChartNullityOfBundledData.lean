import ConstructionTargets.SardCompactProjectedChartImageNullity

open Set MeasureTheory

namespace SardCompactProjectedChartNullityOfBundledData

/-- The paired fiber regularity and identity-projected zero-derivative bundle
directly discharges compact projected-chart nullity. -/
theorem measure_image_zero_of_bundled_inverseSlice_data
    {D X Y G C S : Type*} [TopologicalSpace X]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [Nontrivial S]
    (μY : Measure Y) (μC : Measure C) (μS : Measure S)
    [Measure.IsAddHaarMeasure μY] [Measure.IsAddHaarMeasure μC]
    [Measure.IsAddHaarMeasure μS]
    (hind : ∀ (q : G → S) (u : Set G),
      (∀ z ∈ u, ContDiffAt ℝ 1 q z) →
      μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (chart : OpenPartialHomeomorph X (C × G)) (coord : Y ≃L[ℝ] C × S)
    (f : X → Y) (K : Set X) (hK : IsCompact K) (hKsource : K ⊆ chart.source)
    (hfK : ContinuousOn f K)
    (hfirst : (fun x => (chart x).1) = fun x => (coord (f x)).1)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ D)
    (hdata :
      (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
        ContDiffAt ℝ 1 (fun w : G => (coord (f (chart.symm (c, w)))).2) z) ∧
      (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
        HasFDerivAt
          ((ContinuousLinearMap.id ℝ S) ∘
            fun w : G => (coord (f (chart.symm (c, w)))).2)
          (0 : G →L[ℝ] S) z)) :
    μY (f '' K) = 0 := by
  exact SardCompactProjectedChartImageNullityProbe.measure_image_zero_of_compact_projectedChart
    μY μC μS 1 (fun _ => hind) chart coord f K hK hKsource hfK hfirst
    (ContinuousLinearMap.id ℝ S) hdim (by simp) hdata.1 (fun x => ⟨x, rfl⟩) hdata.2

#print axioms measure_image_zero_of_bundled_inverseSlice_data

end SardCompactProjectedChartNullityOfBundledData
