import ConstructionTargets.SardFiniteOrderPositiveRankPointwiseClosedOpenNullity

open Set MeasureTheory
noncomputable section
namespace SardFiniteOrderPositiveRankExactStratumPointwiseNullityProbe
universe u v

theorem exists_open_rankStratum_image_zero_finiteOrder
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (r order d : ℕ) (hf : ContDiff ℝ order f) (horder : order ≠ 0)
    (x : E) (hxrank : x ∈ rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r)
    (hrpos : 0 < r) (hcrit : ¬ Function.Surjective (fderiv ℝ f x))
    (hind : ∀ e < d, SardClassicalFiniteOrderCriticalNullityPredicateProbe.ClassicalCriticalNullityAtDimension.{u,v} e)
    (hd : Module.finrank ℝ E = d)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) order) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      μF (f '' (rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r ∩ U)) = 0 := by
  obtain ⟨U, hU, hxU, hnull⟩ :=
    SardFiniteOrderPositiveRankPointwiseClosedOpenNullityProbe.exists_open_rankUpper_image_zero_finiteOrder
      μF f r order d hf horder x hxrank hrpos hcrit hind hd hadm
  refine ⟨U, hU, hxU, measure_mono_null ?_ hnull⟩
  rintro y ⟨z, ⟨hzrank, hzU⟩, rfl⟩
  exact ⟨z, ⟨hzrank.le, hzU⟩, rfl⟩

#print axioms exists_open_rankStratum_image_zero_finiteOrder
end SardFiniteOrderPositiveRankExactStratumPointwiseNullityProbe
