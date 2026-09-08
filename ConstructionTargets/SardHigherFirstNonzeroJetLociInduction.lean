import ConstructionTargets.SardFirstNonzeroJetInductiveLocusNullity

open Set MeasureTheory

noncomputable section
namespace SardHigherFirstNonzeroJetLociInductionProbe

universe u v

theorem higher_firstNonzeroJetLoci_image_null_of_induction
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (k : ℕ)
    (n : WithTop ℕ∞) (hn : n ≠ 0)
    (hnTop : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hf1 : ∀ i, 1 ≤ i → i + 1 ≤ k → ContDiff ℝ (i + 1) f)
    (hfn : ∀ i, 1 ≤ i → i + 1 ≤ k → ContDiff ℝ (n + i) f)
    (hind : ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
      [FiniteDimensional ℝ G] [CompleteSpace G],
      Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (q : G → F) (s : Set G),
        (∀ z ∈ s, ContDiffAt ℝ n q z) →
        μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (hKcrit : ∀ y ∈ K, ¬ Function.Surjective (fderiv ℝ f y)) :
    ∀ j ∈ Set.Icc 2 k,
      μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
        f K j) = 0 := by
  intro j hj
  rcases hj with ⟨hj2, hjk⟩
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact SardFirstNonzeroJetInductiveLocusNullityProbe.firstNonzeroJetLocus_image_null_of_induction
    μ f K i (by omega) n hn hnTop (hf1 i (by omega) (by omega))
      (hfn i (by omega) (by omega)) hind hKcrit

#print axioms higher_firstNonzeroJetLoci_image_null_of_induction

end SardHigherFirstNonzeroJetLociInductionProbe
