import Mathlib

open Set

namespace SardHigherJetLocusDecompositionProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Points of `K` where every derivative from order one through `k` vanishes. -/
def flatThrough (f : E → F) (K : Set E) (k : ℕ) : Set E :=
  {x | x ∈ K ∧ ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0}

/-- Points of `K` where the derivative of order `i` is nonzero. -/
def nonzeroJetLocus (f : E → F) (K : Set E) (i : ℕ) : Set E :=
  {x | x ∈ K ∧ iteratedFDeriv ℝ i f x ≠ 0}

/-- A locus splits into the part flat through order `k` and the finite union of
the loci on which one of the first `k` derivatives is nonzero. -/
theorem eq_flatThrough_union_iUnion_nonzeroJetLocus
    (f : E → F) (K : Set E) (k : ℕ) :
    K = flatThrough f K k ∪
      ⋃ i ∈ Set.Icc 1 k, nonzeroJetLocus f K i := by
  ext x
  constructor
  · intro hx
    by_cases hflat : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0
    · exact Or.inl ⟨hx, hflat⟩
    · push_neg at hflat
      obtain ⟨i, hi1, hik, hi⟩ := hflat
      apply Or.inr
      simp only [mem_iUnion, exists_prop]
      exact ⟨i, ⟨hi1, hik⟩, hx, hi⟩
  · rintro (hx | hx)
    · exact hx.1
    · simp only [mem_iUnion, exists_prop] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact hxi.1

#print axioms eq_flatThrough_union_iUnion_nonzeroJetLocus
end SardHigherJetLocusDecompositionProbe
