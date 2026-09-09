import ConstructionTargets.SardHigherFirstNonzeroJetLociInduction

open Set MeasureTheory
universe u v

theorem higher_firstNonzeroJetLoci_null_of_remainingOrder_induction
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (k : ℕ)
    (hf : ContDiff ℝ (k + 1) f)
    (hind : ∀ i, 1 ≤ i → i ≤ k →
      ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
        [FiniteDimensional ℝ G] [CompleteSpace G],
        Module.finrank ℝ G < Module.finrank ℝ E →
        ∀ (q : G → F) (s : Set G),
          (∀ z ∈ s, ContDiffAt ℝ ((k + 1 - i : ℕ) : WithTop ℕ∞) q z) →
          μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (hcrit : ∀ y ∈ K, ¬ Function.Surjective (fderiv ℝ f y)) :
    ∀ j ∈ Set.Icc 2 (k + 1),
      μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K j) = 0 := by
  intro j hj
  rcases hj with ⟨hjlo, hjhi⟩
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hi : i ≤ k := by omega
  apply SardFirstNonzeroJetInductiveLocusNullityProbe.firstNonzeroJetLocus_image_null_of_induction
    μ f K i (by omega) ((k + 1 - i : ℕ) : WithTop ℕ∞)
  · exact_mod_cast (show k + 1 - i ≠ 0 by omega)
  · simp
  · exact hf.of_le (by exact_mod_cast (show i + 1 ≤ k + 1 by omega))
  · have heq : (↑(k + 1 - i) : WithTop ℕ∞) + ↑i = ↑(k + 1) := by
      rw [← Nat.cast_add]
      congr 1
      omega
    rw [heq]
    exact hf
  · exact hind i (by omega) hi
  · exact hcrit

#print axioms higher_firstNonzeroJetLoci_null_of_remainingOrder_induction
