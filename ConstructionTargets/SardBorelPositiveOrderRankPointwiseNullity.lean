import ConstructionTargets.SardBorelPositiveOrderOrthogonalChartNullity
import ConstructionTargets.SardFiniteOrderProjectedSmoothChartTargetData
import ConstructionTargets.SardFiniteOrderProjectedChartLocalizedResidualSliceZero
import ConstructionTargets.SardProjectedChartResidualSlicesContDiffOn
import ConstructionTargets.SardRangeProjectionCoordinateDerivative
import ConstructionTargets.SardProjectedRankReducedDimensionIdentities
import ConstructionTargets.SardProjectedRangeKernelDimensionDrop
import ConstructionTargets.SardProjectedPositiveRankDimensionData
import ConstructionTargets.SardDerivativeRankUpperLocusClosed

open Set MeasureTheory
noncomputable section
namespace SardBorelPositiveOrderRankPointwiseNullityProbe
universe u v

theorem exists_open_rankUpper_image_zero_positiveOrder
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (r order d : ℕ) (hf : ContDiff ℝ order f) (horder : order ≠ 0)
    (x : E) (hxrank : x ∈ rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)
    (hrpos : 0 < r) (hcrit : ¬ Function.Surjective (fderiv ℝ f x))
    (hind : ∀ e < d, BorelPositiveOrderCriticalNullityAtDimension.{u,v} e)
    (hd : Module.finrank ℝ E = d)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) order) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ μF (f '' ({y | Module.finrank ℝ
      (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ U)) = 0 := by
  let L := fderiv ℝ f x
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder)
  have hstrict : HasStrictFDerivAt f L x :=
    hf1.contDiffAt.hasStrictFDerivAt' (hf1.differentiable one_ne_zero x).hasFDerivAt one_ne_zero
  obtain ⟨chart, hxsource, hfirst, hchart, hsymm, hsurj⟩ :=
    SardFiniteOrderProjectedSmoothChartTargetDataProbe.exists_projected_finiteOrderChart_target_data
      f x L order horder hstrict hf.contDiffAt
  let A : Set E := {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r}
  let G := ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker
  obtain ⟨hsource, htarget⟩ :=
    SardProjectedRankReducedDimensionIdentitiesProbe.projected_rank_reduced_finranks L r hxrank
  obtain ⟨hrSource, hrTarget, hdrop⟩ :=
    SardProjectedPositiveRankDimensionDataProbe.projected_positiveRank_dimension_data L r hxrank hrpos
  refine ⟨chart.source, chart.open_source, hxsource, ?_⟩
  apply SardBorelPositiveOrderOrthogonalChartNullityProbe.measure_image_zero_of_rangeOrthogonal_closedOpenChart_positiveOrder
    μF L hcrit d (Module.finrank ℝ E) (Module.finrank ℝ F) r order hind hsource htarget
      hadm hrSource hrTarget chart f A chart.source
      (SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost f r hf1)
      chart.open_source (fun _ h => h) hf.continuous.continuousOn
      hfirst hd (by simpa [G] using (hd ▸ hdrop)) horder
  · intro c z hcz hlocus
    simpa [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply] using
      SardProjectedChartResidualSlicesContDiffOnProbe.contDiffAt_residual_inverseSlices_of_contDiffOn
        chart f ((LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection) order hsymm hf.contDiffOn c z hcz
  · let P := (LinearMap.range L.toLinearMap).orthogonalProjection
    let Q := (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection
    have hp : ContDiffOn ℝ order (fun y => P (f y)) chart.source := P.contDiff.comp_contDiffOn hf.contDiffOn
    have hc : ∀ y ∈ chart.source, fderiv ℝ (fun z => P (f z)) y = P.comp (fderiv ℝ f y) := by
      intro y hy
      exact (SardRangeProjectionCoordinateDerivativeProbe.hasFDerivAt_rangeProjection_comp
        f y (fderiv ℝ f y) L (hf1.differentiable one_ne_zero y).hasFDerivAt).fderiv
    have hz := SardFiniteOrderProjectedChartLocalizedResidualSliceZeroProbe.forall_hasFDerivAt_zero_residual_inverseSlice_on_locus_finiteOrder
      order horder chart f (fun y => P (f y)) A chart.source
      (by simpa [P, SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply] using hfirst)
      hsymm hf.contDiffOn hp L P Q r hxrank rfl (fun y hy hyl => hyl.1) hc
      (fun y hy => hsurj y hy (fderiv ℝ f y) (hf1.differentiable one_ne_zero y).hasFDerivAt)
    intro c z hcz hlocus
    simpa [P, Q, Function.comp_def, SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply] using
      hz c z hcz hlocus

#print axioms exists_open_rankUpper_image_zero_positiveOrder
end SardBorelPositiveOrderRankPointwiseNullityProbe
