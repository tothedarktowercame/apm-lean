import ConstructionTargets.SardDerivativeRangeOrthogonalClosedOpenChartNullity
import ConstructionTargets.SardProjectedChartLocalizedResidualSliceZero
import ConstructionTargets.SardProjectedChartResidualSlicesContDiffOn
import ConstructionTargets.SardRangeProjectionCoordinateDerivative
import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv

open Set MeasureTheory

noncomputable section

namespace SardExactRankClosedOpenProjectedChartNullityProbe

/-- Concrete derivative-coordinate closed-in-open nullity from a smooth
projected chart and a rank bound localized to the closed locus. -/
theorem measure_image_zero_of_exactRank_closedOpen_projectedChart
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (hf : ContDiff ℝ 1 f) (L : E →L[ℝ] F)
    (hL : ¬ Function.Surjective L) (r : ℕ)
    (hbase : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hind : ∀ (μS : Measure (LinearMap.range L.toLinearMap)ᗮ),
      Measure.IsAddHaarMeasure μS →
      ∀ (q : G → (LinearMap.range L.toLinearMap)ᗮ) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ 1 q z) →
        μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (chart : OpenPartialHomeomorph E ((LinearMap.range L.toLinearMap) × G))
    (A U : Set E) (hA : IsClosed A) (hU : IsOpen U)
    (hUsource : U ⊆ chart.source)
    (hfirst : (fun x => (chart x).1) = fun x =>
      (LinearMap.range L.toLinearMap).orthogonalProjection (f x))
    (hsymm : ContDiffOn ℝ 1 chart.symm chart.target)
    (hsurj : ∀ x ∈ chart.source,
      (((LinearMap.range L.toLinearMap).orthogonalProjection).comp
        (fderiv ℝ f x)).range = ⊤)
    (hrank : ∀ x ∈ chart.source, x ∈ A ∩ U →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r)
    (hdim : Module.finrank ℝ G < Module.finrank ℝ E) :
    μF (f '' (A ∩ U)) = 0 := by
  let P : F →L[ℝ] (LinearMap.range L.toLinearMap) :=
    (LinearMap.range L.toLinearMap).orthogonalProjection
  let Q : F →L[ℝ] (LinearMap.range L.toLinearMap)ᗮ :=
    (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection
  have hfs : ContDiffOn ℝ 1 f chart.source := hf.contDiffOn
  have hp : ContDiffOn ℝ 1 (fun x => P (f x)) chart.source := by
    intro x hx
    exact (P.contDiff.contDiffAt.comp x hf.contDiffAt).contDiffWithinAt
  have hcoord : ∀ x ∈ chart.source,
      fderiv ℝ (fun y => P (f y)) x = P.comp (fderiv ℝ f x) := by
    intro x hx
    exact (SardRangeProjectionCoordinateDerivativeProbe.hasFDerivAt_rangeProjection_comp
      f x (fderiv ℝ f x) L (hf.differentiable one_ne_zero x).hasFDerivAt).fderiv
  have hz := SardProjectedChartLocalizedResidualSliceZeroProbe.forall_hasFDerivAt_zero_residual_inverseSlice_on_locus
    chart f (fun x => P (f x)) A U hfirst hsymm hfs hp L P Q r hbase rfl
    hrank hcoord hsurj
  apply SardDerivativeRangeOrthogonalClosedOpenChartNullityProbe.measure_image_zero_of_rangeOrthogonal_closedOpenChart
    μF L hL hind chart f A U hA hU hUsource (hf.continuous.continuousOn)
  · simpa only [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply] using hfirst
  · exact hdim
  · intro c z hcz hlocus
    have hreg := SardProjectedChartResidualSlicesContDiffOnProbe.contDiffAt_residual_inverseSlices_of_contDiffOn
      chart f Q 1 hsymm hfs c z hcz
    simpa only [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply] using hreg
  · intro c z hcz hlocus
    have hz' := hz c z hcz hlocus
    simpa only [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply,
      Function.comp_apply, ContinuousLinearMap.id_apply] using hz'

#print axioms measure_image_zero_of_exactRank_closedOpen_projectedChart

end SardExactRankClosedOpenProjectedChartNullityProbe
