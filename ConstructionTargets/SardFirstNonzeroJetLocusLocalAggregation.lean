import ConstructionTargets.SardFirstNonzeroJetLocalInductiveNullity
import ConstructionTargets.SardLocalNullitySecondCountableAggregation

open Set MeasureTheory

namespace SardFirstNonzeroJetLocusLocalAggregationProbe

/-- Pointwise null implicit-chart pieces aggregate to nullity of an entire
refined first-nonzero-jet locus in a second-countable source. -/
theorem firstNonzeroJetLocus_image_null_of_locally_image_null
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (i : ℕ)
    (hlocal : ∀ x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K i,
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
        μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
          f K i ∩ U)) = 0) :
    μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
      f K i) = 0 := by
  classical
  let U : E → Set E := fun x =>
    if hx : x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K i
    then (hlocal x hx).choose else Set.univ
  apply SardLocalNullitySecondCountableAggregationProbe.image_null_of_locally_image_null
    μ f (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K i) U
  · intro x hx
    simpa [U, hx] using (hlocal x hx).choose_spec.1
  · intro x hx
    simpa [U, hx] using (hlocal x hx).choose_spec.2.1
  · intro x hx
    simpa [U, hx] using (hlocal x hx).choose_spec.2.2

#print axioms firstNonzeroJetLocus_image_null_of_locally_image_null
end SardFirstNonzeroJetLocusLocalAggregationProbe
