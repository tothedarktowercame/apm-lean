import Mathlib

/-! # Arbitrarily small measure bounds imply nullity -/

open MeasureTheory

/-- A fixed measurable-space set whose measure is bounded by every inverse
natural number has measure zero. -/
theorem measure_eq_zero_of_le_inv_nat
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (hsmall : ∀ n : ℕ, μ s ≤ (n : ENNReal)⁻¹) :
    μ s = 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
  exact (not_lt_of_ge (hsmall n)) hn

#print axioms measure_eq_zero_of_le_inv_nat
