import ConstructionTargets.SardDerivativeRangeOrthogonalClosedOpenChartNullity
import ConstructionTargets.SardFiniteOrderProjectedChartLocalizedResidualSliceZero
import ConstructionTargets.SardProjectedChartResidualSlicesContDiffOn
import ConstructionTargets.SardRangeProjectionCoordinateDerivative
import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv

open Set MeasureTheory
noncomputable section
namespace SardFiniteOrderExactRankClosedOpenProjectedChartNullityProbe

theorem measure_image_zero_of_exactRank_closedOpen_projectedChart_finiteOrder
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (order : ℕ) (horder : order ≠ 0)
    (f : E → F) (hf : ContDiff ℝ order f) (L : E →L[ℝ] F)
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
    (hsymm : ContDiffOn ℝ order chart.symm chart.target)
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
  have hfs : ContDiffOn ℝ order f chart.source := hf.contDiffOn
  have hp : ContDiffOn ℝ order (fun x => P (f x)) chart.source := by
    exact P.contDiff.comp_contDiffOn hfs
  have hcoord : ∀ x ∈ chart.source,
      fderiv ℝ (fun y => P (f y)) x = P.comp (fderiv ℝ f x) := by
    intro x hx
    exact (SardRangeProjectionCoordinateDerivativeProbe.hasFDerivAt_rangeProjection_comp
      f x (fderiv ℝ f x) L
      ((hf.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder)).differentiable
        one_ne_zero x).hasFDerivAt).fderiv
  have hz := SardFiniteOrderProjectedChartLocalizedResidualSliceZeroProbe.forall_hasFDerivAt_zero_residual_inverseSlice_on_locus_finiteOrder
    order horder chart f (fun x => P (f x)) A U hfirst hsymm hfs hp L P Q r hbase rfl
    hrank hcoord hsurj
  apply SardDerivativeRangeOrthogonalClosedOpenChartNullityProbe.measure_image_zero_of_rangeOrthogonal_closedOpenChart
    μF L hL hind chart f A U hA hU hUsource
      ((hf.of_le (show (1 : WithTop ℕ∞) ≤ order by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder)).continuous.continuousOn)
  · simpa only [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply] using hfirst
  · exact hdim
  · intro c z hcz hlocus
    have hreg := SardProjectedChartResidualSlicesContDiffOnProbe.contDiffAt_residual_inverseSlices_of_contDiffOn
      chart f Q order hsymm hfs c z hcz
    simpa only [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply] using
      hreg.of_le (show (1 : WithTop ℕ∞) ≤ order by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder)
  · intro c z hcz hlocus
    have hz' := hz c z hcz hlocus
    simpa only [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply,
      Function.comp_apply, ContinuousLinearMap.id_apply] using hz'

#print axioms measure_image_zero_of_exactRank_closedOpen_projectedChart_finiteOrder
end SardFiniteOrderExactRankClosedOpenProjectedChartNullityProbe
