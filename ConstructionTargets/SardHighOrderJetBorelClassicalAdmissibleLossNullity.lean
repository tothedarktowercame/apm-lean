import ConstructionTargets.SardFirstNonzeroJetInductiveLocusNullity
import ConstructionTargets.SardHighOrderPredicate

open Set MeasureTheory SardClassicalRegularityAdmissibilityProbe
universe u v

theorem highOrder_firstNonzeroJet_image_null_of_borel_classical_admissible_loss
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (f : E → F) (K : Set E)
    (k i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k)
    (hf : ContDiff ℝ (k + 1) f)
    (hbudget : Module.finrank ℝ E + i ≤ Module.finrank ℝ F + (k + 1))
    (hind : ∀ e < Module.finrank ℝ E,
      SardHighOrderPredicateProbe.HighOrderNullityAtDimension.{u,v} e)
    (hcrit : ∀ x ∈ K, ¬ Function.Surjective (fderiv ℝ f x))
    (hT : SardHighOrderPredicateProbe.sardHighOrderThreshold (Module.finrank ℝ E) ≤ k + 2)
    (hile : i + 2 ≤ Module.finrank ℝ E) :
    μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i + 1)) = 0 := by
  apply SardFirstNonzeroJetInductiveLocusNullityProbe.firstNonzeroJetLocus_image_null_of_induction
    μ f K i hi ((k + 1 - i : ℕ) : WithTop ℕ∞)
  · exact_mod_cast (show k + 1 - i ≠ 0 by omega)
  · simp
  · exact hf.of_le (by exact_mod_cast (show i + 1 ≤ k + 1 by omega))
  · have heq : (↑(k + 1 - i) : WithTop ℕ∞) + ↑i = ↑(k + 1) := by
      rw [← Nat.cast_add]
      congr 1
      omega
    rw [heq]
    exact hf
  · intro G _ _ _ _ hdim q s hq
    refine hind _ hdim G rfl F μ inferInstance (k + 1 - i) ?_ ?_ q s hq
    · unfold SardOrderAdmissible
      omega
    · -- threshold side condition: `T (finrank G) ≤ k + 1 - i`
      have hmono : (Module.finrank ℝ G) * (Module.finrank ℝ G + 1) + 2 ≤
          (Module.finrank ℝ E) * (Module.finrank ℝ E + 1) + 2 := by
        have h := SardHighOrderPredicateProbe.sardHighOrderThreshold_mono hdim.le
        exact h
      unfold SardHighOrderPredicateProbe.sardHighOrderThreshold at hT ⊢
      have hkey : (Module.finrank ℝ G) * (Module.finrank ℝ G + 1) + 2 + i ≤
          (Module.finrank ℝ E) * (Module.finrank ℝ E + 1) + 1 := by
        have h1 : (Module.finrank ℝ G : ℤ) + 1 ≤ (Module.finrank ℝ E : ℤ) := by
          exact_mod_cast hdim
        have h2 : (i : ℤ) + 2 ≤ (Module.finrank ℝ E : ℤ) := by exact_mod_cast hile
        have hprod : ((Module.finrank ℝ E : ℤ) - (Module.finrank ℝ G : ℤ)) *
            ((Module.finrank ℝ E : ℤ) + (Module.finrank ℝ G : ℤ) + 1) =
            (Module.finrank ℝ E : ℤ) * ((Module.finrank ℝ E : ℤ) + 1) -
            (Module.finrank ℝ G : ℤ) * ((Module.finrank ℝ G : ℤ) + 1) := by ring
        have hge : (i : ℤ) + 1 ≤ ((Module.finrank ℝ E : ℤ) - (Module.finrank ℝ G : ℤ)) *
            ((Module.finrank ℝ E : ℤ) + (Module.finrank ℝ G : ℤ) + 1) := by
          have hA : (1 : ℤ) ≤ (Module.finrank ℝ E : ℤ) - (Module.finrank ℝ G : ℤ) := by
            linarith
          have hB : (i : ℤ) + 1 ≤ (Module.finrank ℝ E : ℤ) +
              (Module.finrank ℝ G : ℤ) + 1 := by linarith
          have hAB : (1 : ℤ) * ((i : ℤ) + 1) ≤
              ((Module.finrank ℝ E : ℤ) - (Module.finrank ℝ G : ℤ)) *
              ((Module.finrank ℝ E : ℤ) + (Module.finrank ℝ G : ℤ) + 1) :=
            mul_le_mul hA hB (by linarith) (by linarith)
          nlinarith [h1, h2, hAB]
        have hkey' : (Module.finrank ℝ G : ℤ) * ((Module.finrank ℝ G : ℤ) + 1) + 2 + i ≤
            (Module.finrank ℝ E : ℤ) * ((Module.finrank ℝ E : ℤ) + 1) + 1 := by
          linarith
        exact_mod_cast hkey'
      omega
  · exact hcrit

#print axioms highOrder_firstNonzeroJet_image_null_of_borel_classical_admissible_loss
