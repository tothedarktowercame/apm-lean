import ConstructionTargets.SardHighOrderOverlapNormedSpaces

open Set MeasureTheory
universe u v

/-- Strong induction closure of the high-order Sard predicate: no `hremaining`
is needed, because for orders above the threshold `T d = d * (d + 1) + 2` the
overlap hypothesis always holds. -/
theorem highOrder_nullityAtDimension_of_strong_induction :
    ∀ d, SardHighOrderPredicateProbe.HighOrderNullityAtDimension.{u,v} d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro E _ _ _ hd F _ _ _ _ _ μ hμ order hadm hT f s hf
    letI := hμ
    have htwo : 2 ≤ order := by
      have : d + 2 ≤ order := by
        unfold SardHighOrderPredicateProbe.sardHighOrderThreshold at hT
        nlinarith
      omega
    obtain ⟨k, hk⟩ : ∃ k, order = k + 2 := ⟨order - 2, by omega⟩
    subst order
    have hoverlap : Module.finrank ℝ E + (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤
        Module.finrank ℝ F + (k + 2) + 1 := by
      have hdiv : (Module.finrank ℝ E - 1) / Module.finrank ℝ F ≤ Module.finrank ℝ E - 1 :=
        Nat.div_le_self _ _
      rw [← hd] at hT
      unfold SardHighOrderPredicateProbe.sardHighOrderThreshold at hT
      have hA : Module.finrank ℝ E * (Module.finrank ℝ E + 1) =
          Module.finrank ℝ E * Module.finrank ℝ E + Module.finrank ℝ E := by ring
      have hsq : Module.finrank ℝ E ≤
          Module.finrank ℝ E * Module.finrank ℝ E := by
        rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with h0 | hp
        · simp [h0]
        · exact Nat.le_mul_of_pos_left _ hp
      omega
    exact highOrder_localSet_criticalImage_zero_of_borel_overlap_normed_spaces
      μ f s k hf (by simpa only [hd] using hadm) (by simpa only [hd] using ih)
      (by simpa only [hd] using hT) hoverlap

/-- Unconditional finite-order Sard theorem: a `C^order` map between
finite-dimensional real normed spaces sends its critical set to a null set
whenever `order` is at least `d * (d + 1) + 2` with `d` the source dimension. -/
theorem critical_image_null_of_high_order
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (mu : Measure F) [mu.IsAddHaarMeasure]
    (f : E → F) (s : Set E) (order : ℕ)
    (horder : SardHighOrderPredicateProbe.sardHighOrderThreshold
      (Module.finrank ℝ E) ≤ order)
    (hf : ∀ x ∈ s, ContDiffAt ℝ order f x) :
    mu (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  have hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) order := by
    unfold SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
    unfold SardHighOrderPredicateProbe.sardHighOrderThreshold at horder
    have hle : Module.finrank ℝ E + 2 ≤ order := by nlinarith
    omega
  exact highOrder_nullityAtDimension_of_strong_induction (Module.finrank ℝ E)
    E rfl F mu inferInstance order hadm horder f s hf

#print axioms highOrder_nullityAtDimension_of_strong_induction
#print axioms critical_image_null_of_high_order
