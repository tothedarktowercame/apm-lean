import ConstructionTargets.SardFiniteOrderClosedOpenExplicitTopologyMeasureSpaces
import ConstructionTargets.SardDerivativeRangeCoordinateTopologyPackage
import ConstructionTargets.SardDerivativeRangeInheritedBorelSpace
import ConstructionTargets.SardDerivativeRangeInheritedBorelAddHaarPackage
import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv
import ConstructionTargets.SardRankDropRegularityAdmissibility
import ConstructionTargets.SardBorelReducedDimensionInductionNullity

open Set MeasureTheory
noncomputable section
namespace SardBorelDerivativeRangeOrthogonalClosedOpenChartNullityProbe
universe u v

theorem measure_image_zero_of_rangeOrthogonal_closedOpenChart_finiteOrder
    {E G : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (L : E →L[ℝ] F) (hL : ¬ Function.Surjective L)
    (d sourceDim targetDim rank order : ℕ)
    (hind : ∀ e : ℕ, e < d →
      SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension.{u,v} e)
    (hsource : Module.finrank ℝ G = sourceDim - rank)
    (htarget : Module.finrank ℝ (LinearMap.range L.toLinearMap)ᗮ = targetDim - rank)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible sourceDim targetDim order)
    (hrSource : rank ≤ sourceDim) (hrTarget : rank ≤ targetDim)
    (chart : OpenPartialHomeomorph E ((LinearMap.range L.toLinearMap) × G))
    (f : E → F) (A U : Set E) (hA : IsClosed A) (hU : IsOpen U)
    (hUsource : U ⊆ chart.source) (hf : ContinuousOn f (A ∩ U))
    (hfirst : (fun x => (chart x).1) = fun x =>
      (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
        (LinearMap.range L.toLinearMap) (f x)).1)
    (hd : Module.finrank ℝ E = d) (hdim : Module.finrank ℝ G < d) (horder : order ≠ 0)
    (hq : ∀ c z, (c, z) ∈ chart.target → chart.symm (c, z) ∈ A ∩ U →
      ContDiffAt ℝ order (fun w : G =>
        (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
          (LinearMap.range L.toLinearMap) (f (chart.symm (c, w)))).2) z)
    (hzero : ∀ c z, (c, z) ∈ chart.target → chart.symm (c, z) ∈ A ∩ U →
      HasFDerivAt ((ContinuousLinearMap.id ℝ (LinearMap.range L.toLinearMap)ᗮ) ∘
        fun w : G => (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
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
  obtain ⟨hBR, hBS⟩ := SardDerivativeRangeInheritedBorelSpaceProbe.range_orthogonal_inherited_borelSpace L
  letI : @BorelSpace (LinearMap.range L.toLinearMap) inferInstance inferInstance := hBR
  letI : @BorelSpace (LinearMap.range L.toLinearMap)ᗮ inferInstance inferInstance := hBS
  letI : Nontrivial (LinearMap.range L.toLinearMap)ᗮ :=
    SardNonsurjectiveDerivativeOrthogonalNontrivialProbe.nontrivial_range_orthogonal_of_not_surjective L hL
  let μR : Measure (LinearMap.range L.toLinearMap) := Measure.addHaar
  let μS : Measure (LinearMap.range L.toLinearMap)ᗮ := Measure.addHaar
  letI : Measure.IsAddHaarMeasure μR := inferInstance
  letI : Measure.IsAddHaarMeasure μS := inferInstance
  have hμF : Measure.IsAddHaarMeasure μF := inferInstance
  have hμR : Measure.IsAddHaarMeasure μR := inferInstance
  have hμS : Measure.IsAddHaarMeasure μS := inferInstance
  apply SardFiniteOrderClosedOpenExplicitTopologyMeasureSpacesProbe.measure_image_zero_of_closedOpen_explicit_topology_measureSpaces
    (D := E) hLCR hSCR hLCS hSCS inferInstance inferInstance hBR hBS
    μF μR μS hμF hμR hμS order horder
    (fun hdim' => @SardBorelReducedDimensionInductionNullityProbe.reducedDimension_slice_nullity
      G _ _ _ (LinearMap.range L.toLinearMap)ᗮ _ _ _ _ hBS
      μS hμS d sourceDim targetDim rank order hind (hd ▸ hdim')
      hsource htarget hadm hrSource hrTarget)
    chart (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates
      (LinearMap.range L.toLinearMap)) f A U hA hU hUsource hf hfirst
    (ContinuousLinearMap.id ℝ (LinearMap.range L.toLinearMap)ᗮ) (hd.symm ▸ hdim)
      Function.surjective_id hq hzero

#print axioms measure_image_zero_of_rangeOrthogonal_closedOpenChart_finiteOrder
end SardBorelDerivativeRangeOrthogonalClosedOpenChartNullityProbe
