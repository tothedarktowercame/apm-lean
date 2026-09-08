import ConstructionTargets.SardCompactProjectedChartNullityOfBundledData
import ConstructionTargets.SardDerivativeRangeInheritedBorelAddHaarPackage
import ConstructionTargets.SardDerivativeRangeInheritedBorelSpace
import ConstructionTargets.SardDerivativeRangeCoordinateTopologyPackage
import ConstructionTargets.SardTargetOrthogonalCoordinateInverseSliceNullityData

open Set MeasureTheory

noncomputable section

namespace SardDerivativeRangeOrthogonalCompactChartNullityProbe

/-- Inherited coordinate measures and canonical target-coordinate slice data
instantiate compact projected-chart nullity at a nonsurjective derivative. -/
theorem measure_image_zero_of_rangeOrthogonal_compactChart
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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
    (f : E → F) (K : Set E) (hK : IsCompact K) (hKsource : K ⊆ chart.source)
    (hfK : ContinuousOn f K)
    (hfirst : (fun x => (chart x).1) =
      fun x => (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
        (LinearMap.range L.toLinearMap) (f x)).1)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ E)
    (hdata :
      (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
        ContDiffAt ℝ 1
          (fun w : G => (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection
            (f (chart.symm (c, w)))) z) ∧
      (∀ c z, z ∈ {z | (c, z) ∈ chart.target} →
        HasFDerivAt
          ((ContinuousLinearMap.id ℝ (LinearMap.range L.toLinearMap)ᗮ) ∘
            fun w : G => (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection
              (f (chart.symm (c, w))))
          (0 : G →L[ℝ] (LinearMap.range L.toLinearMap)ᗮ) z)) :
    μF (f '' K) = 0 := by
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
  have _ : BorelSpace (LinearMap.range L.toLinearMap) := inferInstance
  exact @SardCompactProjectedChartNullityOfBundledDataProbe.measure_image_zero_of_bundled_inverseSlice_data
    E E F G (LinearMap.range L.toLinearMap) (LinearMap.range L.toLinearMap)ᗮ
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance hBR hLCR hSCR
    inferInstance inferInstance inferInstance hBS hLCS hSCS inferInstance
    μF μR μS inferInstance hμR hμS (hind μS hμS) chart
    (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
      (LinearMap.range L.toLinearMap)) f K hK hKsource hfK hfirst hdim
    (SardTargetOrthogonalCoordinateInverseSliceNullityDataProbe.targetOrthogonalCoordinates_inverseSlice_nullity_data
      L chart f hdata)

#print axioms measure_image_zero_of_rangeOrthogonal_compactChart

end SardDerivativeRangeOrthogonalCompactChartNullityProbe
