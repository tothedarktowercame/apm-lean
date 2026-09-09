import ConstructionTargets.SardFirstNonzeroJetInductiveLocusNullity
import ConstructionTargets.SardClassicalFiniteOrderCriticalNullityPredicate

open Set MeasureTheory SardClassicalRegularityAdmissibilityProbe
universe u v

theorem secondJet_image_null_of_classical_lowerDimension_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (f : E → F) (K : Set E) (k : ℕ)
    (hf : ContDiff ℝ (k + 2) f)
    (hadm : SardOrderAdmissible (Module.finrank ℝ E) (Module.finrank ℝ F) (k + 2))
    (hind : ∀ e < Module.finrank ℝ E,
      SardClassicalFiniteOrderCriticalNullityPredicateProbe.ClassicalCriticalNullityAtDimension.{u,v} e)
    (hcrit : ∀ x ∈ K, ¬ Function.Surjective (fderiv ℝ f x)) :
    μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 2) = 0 := by
  apply SardFirstNonzeroJetInductiveLocusNullityProbe.firstNonzeroJetLocus_image_null_of_induction
    μ f K 1 (by omega) ((k + 1 : ℕ) : WithTop ℕ∞)
  · exact_mod_cast (show k + 1 ≠ 0 by omega)
  · simp
  · exact hf.of_le (by norm_cast; omega)
  · have heq : (↑(k + 1) : WithTop ℕ∞) + ↑(1 : ℕ) = ↑(k + 2) := by
      rw [← Nat.cast_add]
    rw [heq]
    exact hf
  · intro G _ _ _ _ hdim q s hq
    apply hind _ hdim G rfl F μ inferInstance (k + 1) ?_ q s hq
    unfold SardOrderAdmissible at *
    omega
  · exact hcrit

#print axioms secondJet_image_null_of_classical_lowerDimension_induction
