import ConstructionTargets.SardBorelOverlapNormedSource
import ConstructionTargets.SardTargetEquivCriticalImage
import ConstructionTargets.SardContinuousLinearEquivImageNullity

open Set MeasureTheory
universe u v

theorem localSet_criticalImage_zero_of_borel_overlap_target_equiv
    {E : Type u} {F H : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (e : F ≃L[ℝ] H) (μ : Measure F) (ν : Measure H)
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (f : E → F) (s : Set E) (k : ℕ)
    (hf : ∀ x ∈ s, ContDiffAt ℝ (k + 2) f x)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hind : ∀ d < Module.finrank ℝ E,
      SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension.{u,v} d)
    (hoverlap : Module.finrank ℝ E + (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤
      Module.finrank ℝ F + (k + 2) + 1) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  have hdim : Module.finrank ℝ F = Module.finrank ℝ H := e.toLinearEquiv.finrank_eq
  have hreg : ∀ x ∈ s, ContDiffAt ℝ (k + 2) (e ∘ f) x := by
    intro x hx
    exact e.contDiff.contDiffAt.comp x (hf x hx)
  have hnull := localSet_criticalImage_zero_of_borel_overlap_normed_source
    ν (e ∘ f) s k hreg (by simpa only [hdim] using hadm) hind
      (by simpa only [hdim] using hoverlap)
  rw [criticalImage_eq_of_target_continuousLinearEquiv e f s
    (fun x hx => (hf x hx).differentiableAt (by norm_cast))] at hnull
  exact SardContinuousLinearEquivImageNullityProbe.ContinuousLinearEquiv.measure_zero_of_image_zero_addHaar
    e μ ν _ hnull

#print axioms localSet_criticalImage_zero_of_borel_overlap_target_equiv
