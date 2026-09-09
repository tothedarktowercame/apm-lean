import ConstructionTargets.SardCriticalImageJetRangeOverlap
import ConstructionTargets.SardOpenRegularityGlobalGermExtension
import ConstructionTargets.SardLocalNullitySecondCountableAggregation

open Set MeasureTheory Filter
open scoped Topology
universe u v

theorem open_criticalImage_zero_of_jet_range_overlap_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (U : Set E) (k : ℕ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ (k + 2) f U)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hind : ∀ e < Module.finrank ℝ E,
      SardClassicalFiniteOrderCriticalNullityPredicateProbe.ClassicalCriticalNullityAtDimension.{u,v} e)
    (hoverlap : Module.finrank ℝ E + (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤
      Module.finrank ℝ F + (k + 2) + 1) :
    μ (f '' (U ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  classical
  let T := U ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)}
  have hlocal : ∀ x : E, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
      (x ∈ T → μ (f '' (T ∩ V)) = 0) := by
    intro x
    by_cases hx : x ∈ T
    · obtain ⟨g, hg, heq⟩ := exists_global_contDiff_germ_of_contDiffOn_open
        f U x (k + 2) hU hx.1 hf
      have hboth := heq.and (heq.fderiv (𝕜 := ℝ))
      obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.1 hboth
      refine ⟨V, hVo, hxV, fun _ => ?_⟩
      have hgnull := criticalImage_zero_of_jet_range_overlap_induction
        μ g univ k hg hadm hind hoverlap
      apply measure_mono_null (t := g '' (univ ∩ {y | ¬ Function.Surjective (fderiv ℝ g y)})) _ hgnull
      rintro z ⟨y, hy, rfl⟩
      obtain ⟨hval, hder⟩ := hVsub hy.2
      refine ⟨y, ⟨mem_univ y, ?_⟩, hval⟩
      change ¬ Function.Surjective (fderiv ℝ g y)
      rw [hder]
      exact hy.1.2
    · exact ⟨univ, isOpen_univ, mem_univ x, fun h => (hx h).elim⟩
  choose V hVo hxV hVnull using hlocal
  exact SardLocalNullitySecondCountableAggregationProbe.image_null_of_locally_image_null
    μ f T V (fun x _ => hVo x) (fun x _ => hxV x) hVnull

#print axioms open_criticalImage_zero_of_jet_range_overlap_induction
