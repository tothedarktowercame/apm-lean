import ConstructionTargets.SardFiniteOrderProjectedSliceLowerDimensionNullity
import ConstructionTargets.SardProjectedSliceDerivativeNonsurjective

open Set MeasureTheory

noncomputable section
namespace SardFiniteOrderProjectedSliceCriticalNullityProbe

universe u v

/-- A surjective target projection with zero derivative makes every point of a
finite-order projected slice critical, so lower-dimensional induction gives
nullity of the whole slice image. -/
theorem image_null_of_lowerDimension_projected_hasFDerivAt_zero
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G]
    {S : Type v} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S]
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]
    (μS : Measure S) (hμS : Measure.IsAddHaarMeasure μS)
    (d sourceDim targetDim rank order : ℕ)
    (hind : ∀ e : ℕ, e < d →
      SardClassicalFiniteOrderCriticalNullityPredicateProbe.ClassicalCriticalNullityAtDimension.{u,v} e)
    (hdim : Module.finrank ℝ G < d)
    (hsource : Module.finrank ℝ G = sourceDim - rank)
    (htarget : Module.finrank ℝ S = targetDim - rank)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (sourceDim - rank) (targetDim - rank) order)
    (q : G → S) (s : Set G) (P : S →L[ℝ] R)
    (horder : order ≠ 0)
    (hq : ∀ z ∈ s, ContDiffAt ℝ order q z)
    (hP : Function.Surjective P)
    (hzero : ∀ z ∈ s, HasFDerivAt (P ∘ q) (0 : G →L[ℝ] R) z) :
    μS (q '' s) = 0 := by
  apply SardFiniteOrderProjectedSliceLowerDimensionNullityProbe.image_null_of_lowerDimension_projectedSlice
    μS hμS d sourceDim targetDim rank order hind hdim hsource htarget hadm q s hq
  intro z hz
  have horder' : (order : WithTop ℕ∞) ≠ 0 := by exact_mod_cast horder
  exact SardProjectedSliceDerivativeNonsurjectiveProbe.not_surjective_fderiv_of_projected_hasFDerivAt_zero
    q z (fderiv ℝ q z) P ((hq z hz).differentiableAt horder').hasFDerivAt hP (hzero z hz)

#print axioms image_null_of_lowerDimension_projected_hasFDerivAt_zero

end SardFiniteOrderProjectedSliceCriticalNullityProbe
