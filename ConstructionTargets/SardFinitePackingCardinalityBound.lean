import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! # Cardinality bound from a finite measurable packing -/

open MeasureTheory Set

/-- A finite pairwise-disjoint measurable packing whose members all have
measure at least `v` and whose union lies in `B` has cardinality-times-`v` at
most the measure of `B`. -/
theorem finset_card_mul_le_measure_of_disjoint
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (A : ι → Set α) (B : Set α) (v : ENNReal)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hdisj : PairwiseDisjoint (↑s : Set ι) A)
    (hlow : ∀ i ∈ s, v ≤ μ (A i))
    (hsub : ⋃ i ∈ s, A i ⊆ B) :
    (s.card : ENNReal) * v ≤ μ B := by
  calc
    (s.card : ENNReal) * v = ∑ i ∈ s, v := by simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, μ (A i) := Finset.sum_le_sum fun i hi => hlow i hi
    _ = μ (⋃ i ∈ s, A i) := (measure_biUnion_finset hdisj hA).symm
    _ ≤ μ B := measure_mono hsub

#print axioms finset_card_mul_le_measure_of_disjoint
