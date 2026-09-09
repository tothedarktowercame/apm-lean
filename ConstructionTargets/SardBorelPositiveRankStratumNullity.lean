import ConstructionTargets.SardBorelPositiveRankPointwiseClosedOpenNullity
import ConstructionTargets.SardFiniteOrderRankLocusLocalAggregation

open Set MeasureTheory
noncomputable section
namespace SardBorelPositiveRankStratumNullityProbe
universe u v

theorem measure_image_zero_of_positive_rankStratum_finiteOrder
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (r order d : ℕ) (hf : ContDiff ℝ order f) (horder : order ≠ 0)
    (hrpos : 0 < r)
    (hcritical : ∀ x ∈ rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r,
      ¬ Function.Surjective (fderiv ℝ f x))
    (hind : ∀ e < d, SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension.{u,v} e)
    (hd : Module.finrank ℝ E = d)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) order) :
    μF (f '' rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) = 0 := by
  apply SardFiniteOrderRankLocusLocalAggregationProbe.measure_image_zero_of_rankLocus_pointwise_open
  intro x hx
  obtain ⟨U, hU, hxU, hnull⟩ :=
    SardBorelPositiveRankPointwiseClosedOpenNullityProbe.exists_open_rankUpper_image_zero_finiteOrder
      μF f r order d hf horder x hx hrpos (hcritical x hx) hind hd hadm
  refine ⟨U, hU, hxU, measure_mono_null ?_ hnull⟩
  rintro y ⟨z, ⟨hzrank, hzU⟩, rfl⟩
  exact ⟨z, ⟨hzrank.le, hzU⟩, rfl⟩

#print axioms measure_image_zero_of_positive_rankStratum_finiteOrder
end SardBorelPositiveRankStratumNullityProbe
