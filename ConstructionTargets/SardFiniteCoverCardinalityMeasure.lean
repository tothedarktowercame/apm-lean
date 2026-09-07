import Mathlib

/-! # Cardinality bound for a finite sum of uniform measure estimates -/

/-- A finite sum whose terms are uniformly bounded is at most the cardinality
of its index set times the uniform bound. -/
theorem finset_sum_le_card_mul
    {ι : Type*} (I : Finset ι) (w : ι → ENNReal) (b : ENNReal)
    (h : ∀ i ∈ I, w i ≤ b) :
    ∑ i ∈ I, w i ≤ I.card * b := by
  calc
    ∑ i ∈ I, w i ≤ ∑ i ∈ I, b := Finset.sum_le_sum fun i hi ↦ h i hi
    _ = I.card * b := by simp

#print axioms finset_sum_le_card_mul
