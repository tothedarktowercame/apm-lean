import ConstructionTargets.SardBorelLocalSetCriticalImageJetRangeOverlap

open Set MeasureTheory Filter
open scoped Topology
universe u v

theorem localSet_criticalImage_zero_of_borel_overlap_all_dimensions
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (s : Set E) (k : ℕ)
    (hf : ∀ x ∈ s, ContDiffAt ℝ (k + 2) f x)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hind : ∀ e < Module.finrank ℝ E,
      SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension.{u,v} e)
    (hoverlap : Module.finrank ℝ E + (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤
      Module.finrank ℝ F + (k + 2) + 1) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  classical
  cases subsingleton_or_nontrivial F with
  | inl hF =>
    letI := hF
    have hempty : s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      exact hx.2 (fun y => ⟨0, Subsingleton.elim _ _⟩)
    simp [hempty]
  | inr hF =>
    letI := hF
    cases subsingleton_or_nontrivial E with
    | inl hE =>
      letI := hE
      exact criticalImage_zero_of_source_finrank_zero_borel μ f s
        ((finrank_zero_iff_forall_zero).2 (fun x => Subsingleton.elim x 0))
    | inr hE =>
      letI := hE
      exact localSet_criticalImage_zero_of_borel_jet_range_overlap_induction
        μ f s k hf hadm hind hoverlap

#print axioms localSet_criticalImage_zero_of_borel_overlap_all_dimensions
