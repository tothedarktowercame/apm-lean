import ConstructionTargets.SardClosedOpenProjectedChartImageNullity

open Set MeasureTheory
namespace SardFiniteOrderClosedOpenProjectedChartImageNullityProbe

theorem measure_image_zero_of_closedOpen_projectedChart_finiteOrder
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
    (order : ℕ) (horder : order ≠ 0)
    (hind : Module.finrank ℝ G < Module.finrank ℝ D →
      ∀ (q : G → S) (u : Set G), (∀ z ∈ u, ContDiffAt ℝ order q z) →
        μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (chart : OpenPartialHomeomorph X (C × G)) (coord : Y ≃L[ℝ] C × S)
    (f : X → Y) (A U : Set X) (hA : IsClosed A) (hU : IsOpen U)
    (hUsource : U ⊆ chart.source) (hf : ContinuousOn f (A ∩ U))
    (hfirst : (fun x => (chart x).1) = fun x => (coord (f x)).1)
    (P : S →L[ℝ] R) (hdim : Module.finrank ℝ G < Module.finrank ℝ D)
    (hP : Function.Surjective P)
    (hq : ∀ c z, (c, z) ∈ chart.target → chart.symm (c, z) ∈ A ∩ U →
      ContDiffAt ℝ order (fun w : G => (coord (f (chart.symm (c, w)))).2) z)
    (hzero : ∀ c z, (c, z) ∈ chart.target → chart.symm (c, z) ∈ A ∩ U →
      HasFDerivAt (P ∘ fun w : G => (coord (f (chart.symm (c, w)))).2)
        (0 : G →L[ℝ] R) z) : μY (f '' (A ∩ U)) = 0 := by
  apply SardClosedOpenProjectedChartImageNullityProbe.measure_image_zero_of_closedOpen_projectedChart
    μY μC μS order hind chart coord f A U hA hU hUsource hf hfirst P hdim
      (by exact_mod_cast horder) hP hq hzero

#print axioms measure_image_zero_of_closedOpen_projectedChart_finiteOrder
end SardFiniteOrderClosedOpenProjectedChartImageNullityProbe
