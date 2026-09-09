import ConstructionTargets.SardClassicalFiniteOrderCriticalNullityPredicate

open Set MeasureTheory

theorem criticalImage_zero_of_source_finrank_zero_borel
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (s : Set E) (hd : Module.finrank ℝ E = 0) :
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
    have hpoint : ∀ x : E, x = 0 := (finrank_zero_iff_forall_zero).1 hd
    apply measure_mono_null (t := {f 0}) _ (measure_singleton (f 0))
    rintro y ⟨x, _, rfl⟩
    simp only [Set.mem_singleton_iff, hpoint x]

#print axioms criticalImage_zero_of_source_finrank_zero_borel
