import ConstructionTargets.SardFiniteOrderClosedOpenLocalRankChartNullity

open Set MeasureTheory

noncomputable section
namespace SardFiniteOrderPointwiseRankChartNullityWitnessProbe

universe u v

theorem exists_open_rankLocus_image_zero_of_finiteOrder_localRankChart
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [MeasurableSpace C] [BorelSpace C] [LocallyCompactSpace C]
    [SecondCountableTopology C]
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {S : Type v} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S]
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    (μY : Measure Y) (μC : Measure C) (μS : Measure S)
    [Measure.IsAddHaarMeasure μY] [Measure.IsAddHaarMeasure μC]
    [Measure.IsAddHaarMeasure μS]
    (chart : OpenPartialHomeomorph X (C × G)) (coord : Y ≃L[ℝ] C × S)
    (f : X → Y) (Q : Y →L[ℝ] S) (P : S →L[ℝ] R)
    (s U : Set X) (x : X) (hx : x ∈ U)
    (hs : IsClosed s) (hU : IsOpen U) (hUsource : U ⊆ chart.source)
    (hfirst : (fun z => (chart z).1) = fun z => (coord (f z)).1)
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
      HasFDerivAt (P ∘ fun w : G => Q (f (chart.symm (c, w))))
        (0 : G →L[ℝ] R) z) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ μY (f '' (s ∩ V)) = 0 := by
  refine ⟨U, hU, hx, ?_⟩
  exact SardFiniteOrderClosedOpenLocalRankChartNullityProbe.measure_image_zero_of_closed_inter_open_finiteOrder_localRankChart
    μY μC μS chart coord f Q P s U hs hU hUsource hfirst hsecond
    d sourceDim targetDim rank order hind hdim hsource htarget horder hsymm hf hadm
    hrSource hrTarget hP hzero

#print axioms exists_open_rankLocus_image_zero_of_finiteOrder_localRankChart

end SardFiniteOrderPointwiseRankChartNullityWitnessProbe
