import ConstructionTargets.SardFiniteOrderPointwiseRankChartNullityWitness
import ConstructionTargets.SardProjectedCoordinateExplicitInheritedBorelData

open Set MeasureTheory

noncomputable section

namespace SardFiniteOrderPointwiseWitnessExplicitMeasurableSpacesProbe

theorem projectedCoordinates_explicit_measurableSpace_borel_bindings
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) :
    let mC : MeasurableSpace (LinearMap.range L.toLinearMap) := inferInstance
    let mS : MeasurableSpace (LinearMap.range L.toLinearMap)ᗮ := inferInstance
    @BorelSpace (LinearMap.range L.toLinearMap) inferInstance mC ∧
      @BorelSpace (LinearMap.range L.toLinearMap)ᗮ inferInstance mS := by
  exact SardProjectedCoordinateExplicitInheritedBorelDataProbe.projectedCoordinates_explicit_inherited_borelData L

universe u v

theorem exists_open_rankLocus_image_zero_explicit_measurableSpaces
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {S : Type v} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [FiniteDimensional ℝ S] [LocallyCompactSpace S] [SecondCountableTopology S]
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    (mC : MeasurableSpace C) (mS : MeasurableSpace S)
    (bC : @BorelSpace C inferInstance mC) (bS : @BorelSpace S inferInstance mS)
    (μY : Measure Y) (μC : @Measure C mC) (μS : @Measure S mS)
    (hμY : Measure.IsAddHaarMeasure μY)
    (hμC : @Measure.IsAddHaarMeasure C inferInstance inferInstance mC μC)
    (hμS : @Measure.IsAddHaarMeasure S inferInstance inferInstance mS μS)
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
    letI := mC
    letI := mS
    letI := bC
    letI := bS
    letI := hμY
    letI := hμC
    letI := hμS
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ μY (f '' (s ∩ V)) = 0 := by
  exact SardFiniteOrderPointwiseRankChartNullityWitnessProbe.exists_open_rankLocus_image_zero_of_finiteOrder_localRankChart
    μY μC μS chart coord f Q P s U x hx hs hU hUsource hfirst hsecond
      d sourceDim targetDim rank order hind hdim hsource htarget horder hsymm hf hadm
      hrSource hrTarget hP hzero

#print axioms projectedCoordinates_explicit_measurableSpace_borel_bindings
#print axioms exists_open_rankLocus_image_zero_explicit_measurableSpaces

end SardFiniteOrderPointwiseWitnessExplicitMeasurableSpacesProbe
