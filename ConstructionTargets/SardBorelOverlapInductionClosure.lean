import ConstructionTargets.SardBorelOverlapNormedSpaces

open Set MeasureTheory
open SardBorelClassicalCriticalNullityPredicateProbe
universe u v

theorem borelClassicalCriticalNullity_of_overlap_complement
    (hremaining : ∀ d : ℕ,
      (∀ c < d, BorelClassicalCriticalNullityAtDimension.{u,v} c) →
      ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E], Module.finrank ℝ E = d →
      ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F],
      ∀ (μ : Measure F), μ.IsAddHaarMeasure →
      ∀ (order : ℕ),
        SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
          d (Module.finrank ℝ F) order →
        (order < 2 ∨ Module.finrank ℝ F + order + 1 <
          d + (d - 1) / Module.finrank ℝ F) →
      ∀ (f : E → F) (s : Set E),
        (∀ x ∈ s, ContDiffAt ℝ order f x) →
        μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0) :
    ∀ d, BorelClassicalCriticalNullityAtDimension.{u,v} d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro E _ _ _ hd F _ _ _ _ _ μ hμ order hadm f s hf
    letI := hμ
    by_cases hlo : order < 2
    · exact hremaining d ih E hd F μ hμ order hadm (Or.inl hlo) f s hf
    by_cases hov : d + (d - 1) / Module.finrank ℝ F ≤
        Module.finrank ℝ F + order + 1
    · obtain ⟨k, hk⟩ : ∃ k, order = k + 2 := ⟨order - 2, by omega⟩
      subst order
      apply localSet_criticalImage_zero_of_borel_overlap_normed_spaces μ f s k hf
      · simpa only [hd] using hadm
      · simpa only [hd] using ih
      · simpa only [hd] using hov
    · exact hremaining d ih E hd F μ hμ order hadm
        (Or.inr (Nat.lt_of_not_ge hov)) f s hf

#print axioms borelClassicalCriticalNullity_of_overlap_complement
