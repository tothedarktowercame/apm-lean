import ConstructionTargets.SardClosedOpenImageNullity

open Set MeasureTheory

namespace SardClosedOpenTargetFiberProjectedSliceImageNullityProbe

/-- Global target-fiber projected-slice data imply nullity on a closed locus
localized to an open chart. -/
theorem measure_image_zero_of_closedOpen_targetFiber_projectedSlices
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
    (e : Y ≃L[ℝ] C × S) (f : X → Y) (A U : Set X)
    (hA : IsClosed A) (hU : IsOpen U) (hf : ContinuousOn f (A ∩ U))
    (q : C → G → S) (s : C → Set G) (P : S →L[ℝ] R)
    (hparam : ∀ r,
      (fun y => (e y).2) '' (f '' (A ∩ U) ∩ {y | (e y).1 = r}) ⊆ q r '' s r)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ D)
    (hn : n ≠ 0)
    (hq : ∀ r z, z ∈ s r → ContDiffAt ℝ n (q r) z)
    (hP : Function.Surjective P)
    (hzero : ∀ r z, z ∈ s r → HasFDerivAt (P ∘ q r) (0 : G →L[ℝ] R) z) :
    μY (f '' (A ∩ U)) = 0 := by
  apply SardClosedOpenImageNullityProbe.measure_image_zero_of_closed_inter_open
    μY f A U hA hU
  intro K hK hKA
  apply SardCompactTargetFiberProjectedSliceImageNullityProbe.measure_image_zero_of_compact_targetFiber_projectedSlices
    μY μC μS n hind e f K hK (hf.mono hKA) q s P
  · intro r
    refine (image_mono ?_).trans (hparam r)
    exact inter_subset_inter_left _ (image_mono hKA)
  · exact hdim
  · exact hn
  · exact hq
  · exact hP
  · exact hzero

#print axioms measure_image_zero_of_closedOpen_targetFiber_projectedSlices

end SardClosedOpenTargetFiberProjectedSliceImageNullityProbe
