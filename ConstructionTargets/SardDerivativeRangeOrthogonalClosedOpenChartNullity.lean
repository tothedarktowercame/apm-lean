import ConstructionTargets.SardClosedOpenProjectedChartImageNullity
import ConstructionTargets.SardDerivativeRangeCoordinateTopologyPackage
import ConstructionTargets.SardDerivativeRangeInheritedBorelSpace
import ConstructionTargets.SardDerivativeRangeInheritedBorelAddHaarPackage
import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv

open Set MeasureTheory

noncomputable section

namespace SardDerivativeRangeOrthogonalClosedOpenChartNullityProbe

/-- The closed-in-open projected-chart theorem specialized to derivative-range
and orthogonal-complement target coordinates. -/
theorem measure_image_zero_of_rangeOrthogonal_closedOpenChart
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (L : E →L[ℝ] F) (hL : ¬ Function.Surjective L)
    (hind : ∀ (μS : Measure (LinearMap.range L.toLinearMap)ᗮ),
      Measure.IsAddHaarMeasure μS →
      ∀ (q : G → (LinearMap.range L.toLinearMap)ᗮ) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ 1 q z) →
        μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (chart : OpenPartialHomeomorph E ((LinearMap.range L.toLinearMap) × G))
    (f : E → F) (A U : Set E) (hA : IsClosed A) (hU : IsOpen U)
    (hUsource : U ⊆ chart.source) (hf : ContinuousOn f (A ∩ U))
    (hfirst : (fun x => (chart x).1) = fun x =>
      (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
        (LinearMap.range L.toLinearMap) (f x)).1)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ E)
    (hq : ∀ c z, (c, z) ∈ chart.target → chart.symm (c, z) ∈ A ∩ U →
      ContDiffAt ℝ 1 (fun w : G =>
        (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
          (LinearMap.range L.toLinearMap) (f (chart.symm (c, w)))).2) z)
    (hzero : ∀ c z, (c, z) ∈ chart.target → chart.symm (c, z) ∈ A ∩ U →
      HasFDerivAt
        ((ContinuousLinearMap.id ℝ (LinearMap.range L.toLinearMap)ᗮ) ∘
          fun w : G =>
            (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
              (LinearMap.range L.toLinearMap) (f (chart.symm (c, w)))).2)
        (0 : G →L[ℝ] (LinearMap.range L.toLinearMap)ᗮ) z) :
    μF (f '' (A ∩ U)) = 0 := by
  obtain ⟨hPR, hSCR, hPS, hSCS⟩ :=
    SardDerivativeRangeCoordinateTopologyPackageProbe.range_orthogonal_topology_package L
  letI : ProperSpace (LinearMap.range L.toLinearMap) := hPR
  letI : SecondCountableTopology (LinearMap.range L.toLinearMap) := hSCR
  letI : ProperSpace (LinearMap.range L.toLinearMap)ᗮ := hPS
  letI : SecondCountableTopology (LinearMap.range L.toLinearMap)ᗮ := hSCS
  let hLCR : LocallyCompactSpace (LinearMap.range L.toLinearMap) := inferInstance
  let hLCS : LocallyCompactSpace (LinearMap.range L.toLinearMap)ᗮ := inferInstance
  obtain ⟨hBR, hBS⟩ :=
    SardDerivativeRangeInheritedBorelSpaceProbe.range_orthogonal_inherited_borelSpace L
  letI : BorelSpace (LinearMap.range L.toLinearMap) := hBR
  letI : BorelSpace (LinearMap.range L.toLinearMap)ᗮ := hBS
  letI : Nontrivial (LinearMap.range L.toLinearMap)ᗮ :=
    SardNonsurjectiveDerivativeOrthogonalNontrivialProbe.nontrivial_range_orthogonal_of_not_surjective L hL
  let μR : Measure (LinearMap.range L.toLinearMap) := Measure.addHaar
  let μS : Measure (LinearMap.range L.toLinearMap)ᗮ := Measure.addHaar
  letI : Measure.IsAddHaarMeasure μR := inferInstance
  letI : Measure.IsAddHaarMeasure μS := inferInstance
  have hμR : Measure.IsAddHaarMeasure μR := inferInstance
  have hμS : Measure.IsAddHaarMeasure μS := inferInstance
  apply (@SardClosedOpenProjectedChartImageNullityProbe.measure_image_zero_of_closedOpen_projectedChart
    E F G (LinearMap.range L.toLinearMap)ᗮ (LinearMap.range L.toLinearMap)
    (LinearMap.range L.toLinearMap)ᗮ E
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance hBR hLCR hSCR
    inferInstance inferInstance inferInstance hBS hLCS hSCS
    μF μR μS inferInstance hμR hμS
    1 (fun hdim' => hind μS inferInstance) chart
    (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
      (LinearMap.range L.toLinearMap)) f A U hA hU hUsource hf hfirst
    (ContinuousLinearMap.id ℝ (LinearMap.range L.toLinearMap)ᗮ) hdim (by simp)
    Function.surjective_id hq)
  exact hzero

#print axioms measure_image_zero_of_rangeOrthogonal_closedOpenChart

end SardDerivativeRangeOrthogonalClosedOpenChartNullityProbe
