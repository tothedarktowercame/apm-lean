import ConstructionTargets.SardFiniteOrderProjectedSliceInductionData
import ConstructionTargets.SardClassicalFiniteOrderCriticalNullityPredicate

open Set MeasureTheory

noncomputable section
namespace SardFiniteOrderProjectedSliceLowerDimensionNullityProbe

universe u v

/-- Strong induction at smaller source finrank applies to a projected residual
slice once every point of the localized slice is critical. -/
theorem image_null_of_lowerDimension_projectedSlice
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G]
    {S : Type v} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S]
    (μS : Measure S) (hμS : Measure.IsAddHaarMeasure μS)
    (d sourceDim targetDim rank order : ℕ)
    (hind : ∀ e : ℕ, e < d →
      SardClassicalFiniteOrderCriticalNullityPredicateProbe.ClassicalCriticalNullityAtDimension.{u,v} e)
    (hdim : Module.finrank ℝ G < d)
    (hsource : Module.finrank ℝ G = sourceDim - rank)
    (htarget : Module.finrank ℝ S = targetDim - rank)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (sourceDim - rank) (targetDim - rank) order)
    (q : G → S) (s : Set G)
    (hq : ∀ z ∈ s, ContDiffAt ℝ order q z)
    (hcritical : ∀ z ∈ s, ¬ Function.Surjective (fderiv ℝ q z)) :
    μS (q '' s) = 0 := by
  have hnull := hind (Module.finrank ℝ G) hdim G rfl S μS hμS order
    (by simpa [hsource, htarget] using hadm) q s hq
  have hset : s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)} = s := by
    ext z
    simp only [mem_inter_iff, mem_setOf_eq]
    exact and_iff_left_of_imp (fun hz => hcritical z hz)
  simpa [hset] using hnull

#print axioms image_null_of_lowerDimension_projectedSlice

end SardFiniteOrderProjectedSliceLowerDimensionNullityProbe
