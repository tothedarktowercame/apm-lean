import ConstructionTargets.SardFirstNonzeroJetLocusDecomposition

open Set MeasureTheory

namespace SardFirstNonzeroJetFiniteAssemblyProbe

/-- Nullity of the flat locus, the first-derivative locus, and every higher
first-nonzero-jet locus assembles to nullity of the localized image. -/
theorem image_null_of_flat_first_and_higher_firstNonzeroJetLoci
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (k : ℕ)
    (hflat : μ (f '' SardHigherJetLocusDecompositionProbe.flatThrough f K k) = 0)
    (hfirst : μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
      f K 1) = 0)
    (hhigher : ∀ i ∈ Set.Icc 2 k,
      μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
        f K i) = 0) :
    μ (f '' K) = 0 := by
  apply SardFirstNonzeroJetLocusDecompositionProbe.image_null_of_flatThrough_and_firstNonzeroJetLoci
    μ f K k hflat
  intro i hi
  rcases eq_or_lt_of_le hi.1 with rfl | hi2
  · exact hfirst
  · exact hhigher i ⟨hi2, hi.2⟩

#print axioms image_null_of_flat_first_and_higher_firstNonzeroJetLoci
end SardFirstNonzeroJetFiniteAssemblyProbe
