import ConstructionTargets.SardClosedOpenTargetFiberProjectedSliceImageNullity
import ConstructionTargets.SardProjectedChartTargetFiberSliceContainment

open Set MeasureTheory

namespace SardClosedOpenProjectedChartImageNullityProbe

/-- A closed locus inside an open projected-chart source has null image when
the lower-dimensional slice hypotheses hold only over that locus. -/
theorem measure_image_zero_of_closedOpen_projectedChart
    {D Y G R C S X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
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
    (f : X → Y) (A U : Set X) (hA : IsClosed A) (hU : IsOpen U)
    (hUsource : U ⊆ chart.source) (hf : ContinuousOn f (A ∩ U))
    (hfirst : (fun x => (chart x).1) = fun x => (coord (f x)).1)
    (P : S →L[ℝ] R) (hdim : Module.finrank ℝ G < Module.finrank ℝ D)
    (hn : n ≠ 0) (hP : Function.Surjective P)
    (hq : ∀ c z, (c, z) ∈ chart.target → chart.symm (c, z) ∈ A ∩ U →
      ContDiffAt ℝ n (fun w : G => (coord (f (chart.symm (c, w)))).2) z)
    (hzero : ∀ c z, (c, z) ∈ chart.target → chart.symm (c, z) ∈ A ∩ U →
      HasFDerivAt
        (P ∘ fun w : G => (coord (f (chart.symm (c, w)))).2)
        (0 : G →L[ℝ] R) z) :
    μY (f '' (A ∩ U)) = 0 := by
  apply SardClosedOpenTargetFiberProjectedSliceImageNullityProbe.measure_image_zero_of_closedOpen_targetFiber_projectedSlices
    μY μC μS n hind coord f A U hA hU hf
    (fun c z => (coord (f (chart.symm (c, z)))).2)
    (fun c => {z | (c, z) ∈ chart.target ∧ chart.symm (c, z) ∈ A ∩ U}) P
  · intro c
    rintro _ ⟨y, ⟨⟨x, hxAU, rfl⟩, hyc⟩, rfl⟩
    have hxsource : x ∈ chart.source := hUsource hxAU.2
    have hc : (coord (f x)).1 = (chart x).1 :=
      (congrFun hfirst x).symm
    have hcx : c = (chart x).1 := hyc ▸ hc
    refine ⟨(chart x).2, ?_, ?_⟩
    · constructor
      · simpa [hcx] using chart.map_source hxsource
      · simpa [hcx, chart.left_inv hxsource] using hxAU
    · simp [hcx, chart.left_inv hxsource]
  · exact hdim
  · exact hn
  · intro c z hz
    exact hq c z hz.1 hz.2
  · exact hP
  · intro c z hz
    exact hzero c z hz.1 hz.2

#print axioms measure_image_zero_of_closedOpen_projectedChart

end SardClosedOpenProjectedChartImageNullityProbe
