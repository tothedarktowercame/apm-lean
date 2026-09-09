import ConstructionTargets.SardFiniteOrderClosedOpenProjectedChartImageNullity

open Set MeasureTheory
namespace SardFiniteOrderClosedOpenExplicitTopologyMeasureSpacesProbe
universe u v

theorem measure_image_zero_of_closedOpen_explicit_topology_measureSpaces
    {D Y G R C S X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    (lcC : LocallyCompactSpace C) (scC : SecondCountableTopology C)
    (lcS : LocallyCompactSpace S) (scS : SecondCountableTopology S)
    (mC : MeasurableSpace C) (mS : MeasurableSpace S)
    (bC : @BorelSpace C inferInstance mC) (bS : @BorelSpace S inferInstance mS)
    (μY : Measure Y) (μC : @Measure C mC) (μS : @Measure S mS)
    (hμY : Measure.IsAddHaarMeasure μY)
    (hμC : @Measure.IsAddHaarMeasure C inferInstance inferInstance mC μC)
    (hμS : @Measure.IsAddHaarMeasure S inferInstance inferInstance mS μS)
    (order : ℕ) (horder : order ≠ 0)
    (hind : Module.finrank ℝ G < Module.finrank ℝ D → ∀ q : G → S, ∀ u : Set G,
      (∀ z ∈ u, ContDiffAt ℝ order q z) →
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
        (0 : G →L[ℝ] R) z) :
    letI := lcC; letI := scC; letI := lcS; letI := scS
    μY (f '' (A ∩ U)) = 0 := by
  letI := hμY
  exact SardFiniteOrderClosedOpenProjectedChartImageNullityProbe.measure_image_zero_of_closedOpen_projectedChart_finiteOrder
    μY μC μS order horder hind chart coord f A U hA hU hUsource hf hfirst P hdim hP hq hzero

#print axioms measure_image_zero_of_closedOpen_explicit_topology_measureSpaces
end SardFiniteOrderClosedOpenExplicitTopologyMeasureSpacesProbe
