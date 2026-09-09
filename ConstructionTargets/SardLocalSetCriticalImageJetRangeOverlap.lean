import ConstructionTargets.SardOpenCriticalImageJetRangeOverlap

open Set MeasureTheory Filter
open scoped Topology
universe u v

theorem localSet_criticalImage_zero_of_jet_range_overlap_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (s : Set E) (k : ℕ)
    (hf : ∀ x ∈ s, ContDiffAt ℝ (k + 2) f x)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hind : ∀ e < Module.finrank ℝ E,
      SardClassicalFiniteOrderCriticalNullityPredicateProbe.ClassicalCriticalNullityAtDimension.{u,v} e)
    (hoverlap : Module.finrank ℝ E + (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤
      Module.finrank ℝ F + (k + 2) + 1) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  classical
  let T := s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)}
  have hlocal : ∀ x : E, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
      (x ∈ T → μ (f '' (T ∩ V)) = 0) := by
    intro x
    by_cases hx : x ∈ T
    · have hreg := (hf x hx.1).eventually (by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using ENat.natCast_ne_coe_top (k + 2))
      obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.1 hreg
      refine ⟨V, hVo, hxV, fun _ => ?_⟩
      have hgnull := open_criticalImage_zero_of_jet_range_overlap_induction
        μ f V k hVo (fun y hy =>
          (show ContDiffAt ℝ (k + 2) f y from hVsub hy).contDiffWithinAt) hadm hind hoverlap
      apply measure_mono_null (Set.image_mono ?_) hgnull
      intro y hy
      exact ⟨hy.2, hy.1.2⟩
    · exact ⟨univ, isOpen_univ, mem_univ x, fun h => (hx h).elim⟩
  choose V hVo hxV hVnull using hlocal
  exact SardLocalNullitySecondCountableAggregationProbe.image_null_of_locally_image_null
    μ f T V (fun x _ => hVo x) (fun x _ => hxV x) hVnull

#print axioms localSet_criticalImage_zero_of_jet_range_overlap_induction
