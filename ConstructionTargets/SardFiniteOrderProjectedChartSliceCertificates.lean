import ConstructionTargets.SardFiniteOrderProjectedSliceInductionData
import ConstructionTargets.SardFiniteOrderProjectedSliceCriticalNullity

open Set MeasureTheory

noncomputable section
namespace SardFiniteOrderProjectedChartSliceCertificatesProbe

universe u v

/-- Finite-order projected chart data and zero residual slice derivatives give
a null-image certificate for every fixed first-coordinate slice. -/
theorem forall_projectedSlice_image_null_of_lowerDimension
    {E F C : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G]
    {S : Type v} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S]
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    (chart : OpenPartialHomeomorph E (C × G)) (f : E → F)
    (Q : F →L[ℝ] S) (P : S →L[ℝ] R)
    (μS : Measure S) (hμS : Measure.IsAddHaarMeasure μS)
    (d sourceDim targetDim rank order : ℕ)
    (hind : ∀ e : ℕ, e < d →
      SardClassicalFiniteOrderCriticalNullityPredicateProbe.ClassicalCriticalNullityAtDimension.{u,v} e)
    (hdim : Module.finrank ℝ G < d)
    (hsource : Module.finrank ℝ G = sourceDim - rank)
    (htarget : Module.finrank ℝ S = targetDim - rank)
    (horder : order ≠ 0)
    (hsymm : ContDiffOn ℝ order chart.symm chart.target)
    (hf : ContDiffOn ℝ order f chart.source)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      sourceDim targetDim order)
    (hrSource : rank ≤ sourceDim) (hrTarget : rank ≤ targetDim)
    (hP : Function.Surjective P)
    (hzero : ∀ c z, (c, z) ∈ chart.target →
      HasFDerivAt
        (P ∘ fun w : G => Q (f (chart.symm (c, w))))
        (0 : G →L[ℝ] R) z) :
    ∀ c, μS ((fun w : G => Q (f (chart.symm (c, w)))) ''
      {z | (c, z) ∈ chart.target}) = 0 := by
  obtain ⟨hreg, hadm'⟩ :=
    SardFiniteOrderProjectedSliceInductionDataProbe.finiteOrder_projectedSlice_induction_data
      chart f Q order sourceDim targetDim rank hsymm hf hadm hrSource hrTarget
  intro c
  apply SardFiniteOrderProjectedSliceCriticalNullityProbe.image_null_of_lowerDimension_projected_hasFDerivAt_zero
    μS hμS d sourceDim targetDim rank order hind hdim hsource htarget hadm'
    (fun w : G => Q (f (chart.symm (c, w)))) {z | (c, z) ∈ chart.target} P
    horder (hreg c) hP
  intro z hz
  exact hzero c z hz

#print axioms forall_projectedSlice_image_null_of_lowerDimension

end SardFiniteOrderProjectedChartSliceCertificatesProbe
