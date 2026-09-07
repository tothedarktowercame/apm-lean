import Mathlib

/-! # Finite-cover measure aggregation for Sard estimates -/

open Set MeasureTheory

/-- The measure of a set covered by a finite indexed family is at most the sum
of the measures of the covering sets. -/
theorem measure_le_finset_sum_of_subset_biUnion
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (I : Finset ι) (u : ι → Set α)
    (hcover : s ⊆ ⋃ i ∈ I, u i) :
    μ s ≤ ∑ i ∈ I, μ (u i) := by
  refine (measure_mono hcover).trans ?_
  exact measure_biUnion_finset_le I u

#print axioms measure_le_finset_sum_of_subset_biUnion
