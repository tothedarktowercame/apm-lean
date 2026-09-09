import ConstructionTargets.SardBorelPositiveOrderRankPointwiseNullity
import ConstructionTargets.SardCriticalRankStrataNull
import ConstructionTargets.SardFiniteOrderRankLocusLocalAggregation

open Set MeasureTheory
noncomputable section
namespace SardBorelPositiveOrderRankAggregationProbe
universe u v

theorem measure_image_zero_of_positive_rankStratum_positiveOrder
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
    (hind : ∀ e < d, BorelPositiveOrderCriticalNullityAtDimension.{u,v} e)
    (hd : Module.finrank ℝ E = d)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) order) :
    μF (f '' rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) = 0 := by
  apply SardFiniteOrderRankLocusLocalAggregationProbe.measure_image_zero_of_rankLocus_pointwise_open
  intro x hx
  obtain ⟨U, hU, hxU, hnull⟩ :=
    SardBorelPositiveOrderRankPointwiseNullityProbe.exists_open_rankUpper_image_zero_positiveOrder
      μF f r order d hf horder x hx hrpos (hcritical x hx) hind hd hadm
  refine ⟨U, hU, hxU, measure_mono_null ?_ hnull⟩
  rintro y ⟨z, ⟨hzrank, hzU⟩, rfl⟩
  exact ⟨z, ⟨hzrank.le, hzU⟩, rfl⟩

#print axioms measure_image_zero_of_positive_rankStratum_positiveOrder
end SardBorelPositiveOrderRankAggregationProbe

open Set MeasureTheory
noncomputable section
namespace SardBorelPositiveOrderRankAggregationProbe
universe u v

theorem measure_criticalImage_zero_of_rankZero_positiveOrder
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (order d : ℕ) (hf : ContDiff ℝ order f) (horder : order ≠ 0)
    (hind : ∀ e < d, BorelPositiveOrderCriticalNullityAtDimension.{u,v} e)
    (hd : Module.finrank ℝ E = d)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) order)
    (hzero : μF (f '' rankStratum (fun y => (fderiv ℝ f y).toLinearMap) 0) = 0) :
    μF (f '' criticalSet (fun y => (fderiv ℝ f y).toLinearMap)) = 0 := by
  apply criticalImage_null_of_rankStrata_null μF f
  intro r
  rcases Nat.eq_zero_or_pos r.val with hr | hr
  · simpa [hr] using hzero
  · have hcritical : ∀ x ∈ rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r.val,
        ¬ Function.Surjective (fderiv ℝ f x) := by
      intro x hx hsurj
      have hrange : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊤ :=
        LinearMap.range_eq_top.mpr hsurj
      have hdim : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) =
          Module.finrank ℝ F := by
        rw [hrange]
        exact finrank_top ℝ F
      have hxrank : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = r.val := hx
      omega
    exact SardBorelPositiveOrderRankAggregationProbe.measure_image_zero_of_positive_rankStratum_positiveOrder
      μF f r.val order d hf horder hr hcritical hind hd hadm

#print axioms measure_criticalImage_zero_of_rankZero_positiveOrder
end SardBorelPositiveOrderRankAggregationProbe
