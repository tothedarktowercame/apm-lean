import ConstructionTargets.SardSourceEquivCriticalImage
import ConstructionTargets.SardBorelOverlapDegenerateDimensions

open Set MeasureTheory
universe u v

theorem localSet_criticalImage_zero_of_borel_overlap_source_equiv
    {E G : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G] [ProperSpace G]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (e : G ≃L[ℝ] E) (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (s : Set E) (k : ℕ)
    (hf : ∀ x ∈ s, ContDiffAt ℝ (k + 2) f x)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hind : ∀ d < Module.finrank ℝ E,
      SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension.{u,v} d)
    (hoverlap : Module.finrank ℝ E + (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤
      Module.finrank ℝ F + (k + 2) + 1) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  have hdim : Module.finrank ℝ G = Module.finrank ℝ E := e.toLinearEquiv.finrank_eq
  have hreg : ∀ z ∈ e ⁻¹' s, ContDiffAt ℝ (k + 2) (f ∘ e) z := by
    intro z hz
    exact (hf (e z) hz).comp z e.contDiff.contDiffAt
  have hnull := localSet_criticalImage_zero_of_borel_overlap_all_dimensions
    μ (f ∘ e) (e ⁻¹' s) k hreg (by simpa [hdim] using hadm)
    (by simpa [hdim] using hind) (by simpa [hdim] using hoverlap)
  rw [criticalImage_eq_of_source_continuousLinearEquiv e f s
    (fun x hx => (hf x hx).differentiableAt (by norm_cast))] at hnull
  exact hnull

#print axioms localSet_criticalImage_zero_of_borel_overlap_source_equiv
