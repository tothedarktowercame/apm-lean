import ConstructionTargets.SardFirstNonzeroJetPointwiseWitnessInstantiation
import ConstructionTargets.SardFirstNonzeroJetLocusLocalAggregation

open Set MeasureTheory

noncomputable section
namespace SardFirstNonzeroJetInductiveLocusNullityProbe

universe u v

/-- Pointwise scalarized implicit-chart induction aggregates to nullity of an
entire higher first-nonzero-jet locus. -/
theorem firstNonzeroJetLocus_image_null_of_induction
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (i : ℕ) (hi : 1 ≤ i)
    (n : WithTop ℕ∞) (hn : n ≠ 0)
    (hnTop : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hf1 : ContDiff ℝ (i + 1) f) (hfn : ContDiff ℝ (n + i) f)
    (hind : ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
      [FiniteDimensional ℝ G] [CompleteSpace G],
      Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (q : G → F) (s : Set G),
        (∀ z ∈ s, ContDiffAt ℝ n q z) →
        μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (hKcrit : ∀ y ∈ K, ¬ Function.Surjective (fderiv ℝ f y)) :
    μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
      f K (i + 1)) = 0 := by
  apply SardFirstNonzeroJetLocusLocalAggregationProbe.firstNonzeroJetLocus_image_null_of_locally_image_null
  intro x hx
  exact SardFirstNonzeroJetPointwiseWitnessInstantiationProbe.exists_open_local_image_null_of_firstNonzeroJet
    μ f K i hi n hn hnTop hf1 hfn hind hKcrit x hx

#print axioms firstNonzeroJetLocus_image_null_of_induction
end SardFirstNonzeroJetInductiveLocusNullityProbe
