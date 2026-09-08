import ConstructionTargets.SardFiniteOrderCompactLocalRankChartNullity
import ConstructionTargets.SardClosedOpenImageNullity

open Set MeasureTheory

noncomputable section
namespace SardFiniteOrderClosedOpenLocalRankChartNullityProbe

universe u v

/-- Compact finite-order local rank-chart nullity aggregates over a closed
locus localized to an open subset of the chart source. -/
theorem measure_image_zero_of_closed_inter_open_finiteOrder_localRankChart
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
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
    (s U : Set X) (hs : IsClosed s) (hU : IsOpen U) (hUsource : U ⊆ chart.source)
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
    μY (f '' (s ∩ U)) = 0 := by
  apply SardClosedOpenImageNullityProbe.measure_image_zero_of_closed_inter_open
    μY f s U hs hU
  intro K hK hKsub
  apply SardFiniteOrderCompactLocalRankChartNullityProbe.measure_image_zero_of_compact_finiteOrder_localRankChart
    μY μC μS chart coord f Q P K hK
  · exact fun x hx => hUsource (hKsub hx).2
  · exact hf.continuousOn.mono (fun x hx => hUsource (hKsub hx).2)
  · exact hfirst
  · exact hsecond
  · exact hind
  · exact hdim
  · exact hsource
  · exact htarget
  · exact horder
  · exact hsymm
  · exact hf
  · exact hadm
  · exact hrSource
  · exact hrTarget
  · exact hP
  · exact hzero

#print axioms measure_image_zero_of_closed_inter_open_finiteOrder_localRankChart

end SardFiniteOrderClosedOpenLocalRankChartNullityProbe
