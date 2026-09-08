import ConstructionTargets.SardFiniteOrderProjectedChartSliceCertificates
import ConstructionTargets.SardFiniteOrderCompactProjectedChartNullity

open Set MeasureTheory

noncomputable section
namespace SardFiniteOrderCompactLocalRankChartNullityProbe

universe u v

/-- Finite-order rank-chart data, lower-dimensional induction, and compact
coordinate-fiber aggregation imply nullity of the compact local image. -/
theorem measure_image_zero_of_compact_finiteOrder_localRankChart
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [MeasurableSpace C] [BorelSpace C] [LocallyCompactSpace C]
    [SecondCountableTopology C]
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G]
    {S : Type v} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S]
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    (μY : Measure Y) (μC : Measure C) (μS : Measure S)
    [Measure.IsAddHaarMeasure μY] [Measure.IsAddHaarMeasure μC]
    [Measure.IsAddHaarMeasure μS]
    (chart : OpenPartialHomeomorph X (C × G)) (coord : Y ≃L[ℝ] C × S)
    (f : X → Y) (Q : Y →L[ℝ] S) (P : S →L[ℝ] R)
    (K : Set X) (hK : IsCompact K) (hKsource : K ⊆ chart.source)
    (hfK : ContinuousOn f K)
    (hfirst : (fun x => (chart x).1) = fun x => (coord (f x)).1)
    (hsecond : ∀ y, (coord y).2 = Q y)
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
    μY (f '' K) = 0 := by
  have hslices :=
    SardFiniteOrderProjectedChartSliceCertificatesProbe.forall_projectedSlice_image_null_of_lowerDimension
      chart f Q P μS inferInstance d sourceDim targetDim rank order hind hdim hsource htarget
      horder hsymm hf hadm hrSource hrTarget hP hzero
  apply SardFiniteOrderCompactProjectedChartNullityProbe.measure_image_zero_of_compact_projectedChart_of_sliceCertificates
    μY μC μS chart coord f K hK hKsource hfK hfirst
  intro c
  simpa only [hsecond] using hslices c

#print axioms measure_image_zero_of_compact_finiteOrder_localRankChart

end SardFiniteOrderCompactLocalRankChartNullityProbe
