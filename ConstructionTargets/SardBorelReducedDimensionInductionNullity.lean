import ConstructionTargets.SardBorelClassicalCriticalNullityPredicate
import ConstructionTargets.SardRankDropRegularityAdmissibility

open Set MeasureTheory
namespace SardBorelReducedDimensionInductionNullityProbe
universe u v

theorem reducedDimension_slice_nullity
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {S : Type v} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
    [MeasurableSpace S] [BorelSpace S] (μS : Measure S) (hμS : Measure.IsAddHaarMeasure μS)
    (d sourceDim targetDim rank order : ℕ)
    (hind : ∀ e < d, SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension.{u,v} e)
    (hdim : Module.finrank ℝ G < d)
    (hsource : Module.finrank ℝ G = sourceDim - rank)
    (htarget : Module.finrank ℝ S = targetDim - rank)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible sourceDim targetDim order)
    (hrSource : rank ≤ sourceDim) (hrTarget : rank ≤ targetDim) :
    ∀ (q : G → S) (u : Set G), (∀ z ∈ u, ContDiffAt ℝ order q z) →
      μS (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0 := by
  have hadm' := SardRankDropRegularityAdmissibilityProbe.sardOrderAdmissible_sub_rank hadm hrSource hrTarget
  exact hind _ hdim G rfl S μS hμS order (by simpa [hsource, htarget] using hadm')

#print axioms reducedDimension_slice_nullity
end SardBorelReducedDimensionInductionNullityProbe
