import ConstructionTargets.SardFirstNonzeroJetInductiveLocusNullity
import ConstructionTargets.SardBorelPositiveOrderCriticalNullity

open Set MeasureTheory SardClassicalRegularityAdmissibilityProbe
universe u v

theorem firstNonzeroJet_image_null_of_borel_positive_order_loss
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
      BorelPositiveOrderCriticalNullityAtDimension.{u,v} e)
    (hcrit : ∀ x ∈ K, ¬ Function.Surjective (fderiv ℝ f x)) :
    μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K (i + 1)) = 0 := by
  have hpos : 1 ≤ k + 1 - i := by omega
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
    apply hind _ hdim G rfl F μ inferInstance (k + 1 - i) hpos ?_ q s hq
    unfold SardOrderAdmissible
    omega
  · exact hcrit

#print axioms firstNonzeroJet_image_null_of_borel_positive_order_loss
