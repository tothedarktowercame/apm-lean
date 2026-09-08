import ConstructionTargets.SardCompactProjectedChartImageNullity
import ConstructionTargets.SardProjectedChartResidualSliceNullityData

open Set MeasureTheory

namespace SardCompactProjectedChartNullityOfResidualDataProbe

/-- The bundled regularity and zero-derivative data discharge the analytic
fiber hypotheses of compact projected-chart nullity. -/
theorem measure_image_zero_of_residualSlice_data
    {D E Y G R C S : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
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
    (hind : Module.finrank ℝ G < Module.finrank ℝ D →
      ∀ (q : G → S) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ 1 q z) →
        μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (chart : OpenPartialHomeomorph E (C × G)) (coord : Y ≃L[ℝ] C × S)
    (f : E → Y) (K : Set E) (hK : IsCompact K) (hKsource : K ⊆ chart.source)
    (hfK : ContinuousOn f K)
    (hfirst : (fun x => (chart x).1) = fun x => (coord (f x)).1)
    (hsymm : ContDiffOn ℝ 1 chart.symm chart.target)
    (hf : ContDiffOn ℝ 1 f chart.source)
    (P : S →L[ℝ] R) (hP : Function.Surjective P)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ D)
    (hzero : ∀ c z, (c, z) ∈ chart.target →
      HasFDerivAt
        (fun w : G => (coord (f (chart.symm (c, w)))).2)
        (0 : G →L[ℝ] S) z) :
    μY (f '' K) = 0 := by
  let Q : Y →L[ℝ] S := (ContinuousLinearMap.snd ℝ C S).comp coord.toContinuousLinearMap
  obtain ⟨hq, hzeroP⟩ :=
    SardProjectedChartResidualSliceNullityDataProbe.residual_inverseSlice_nullity_data
      chart f Q hsymm hf (by simpa [Q] using hzero) P
  apply SardCompactProjectedChartImageNullityProbe.measure_image_zero_of_compact_projectedChart
    μY μC μS 1 hind chart coord f K hK hKsource hfK hfirst P hdim (by simp) hq hP
  simpa [Q] using hzeroP

#print axioms measure_image_zero_of_residualSlice_data

end SardCompactProjectedChartNullityOfResidualDataProbe
