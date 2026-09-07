import ConstructionTargets.SardHigherJetImageNullityAggregation

open Set MeasureTheory

namespace SardFirstNonzeroJetLocusDecompositionProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Points where order `i` is the first nonzero derivative order. -/
def firstNonzeroJetLocus (f : E → F) (K : Set E) (i : ℕ) : Set E :=
  {x | x ∈ K ∧
    (∀ j, 1 ≤ j → j < i → iteratedFDeriv ℝ j f x = 0) ∧
    iteratedFDeriv ℝ i f x ≠ 0}

/-- A localized set is the union of its locus flat through order `k` and the
finite family of loci classified by their first nonzero derivative order. -/
theorem eq_flatThrough_union_iUnion_firstNonzeroJetLocus
    (f : E → F) (K : Set E) (k : ℕ) :
    K = SardHigherJetLocusDecompositionProbe.flatThrough f K k ∪
      ⋃ i ∈ Set.Icc 1 k, firstNonzeroJetLocus f K i := by
  classical
  ext x
  constructor
  · intro hx
    by_cases hflat : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0
    · exact Or.inl ⟨hx, hflat⟩
    · push_neg at hflat
      let P : ℕ → Prop := fun i => 1 ≤ i ∧ i ≤ k ∧ iteratedFDeriv ℝ i f x ≠ 0
      have hP : ∃ i, P i := by
        obtain ⟨i, hi1, hik, hi⟩ := hflat
        exact ⟨i, hi1, hik, hi⟩
      let i := Nat.find hP
      have hi := Nat.find_spec hP
      apply Or.inr
      refine mem_iUnion_of_mem i (mem_iUnion_of_mem ⟨hi.1, hi.2.1⟩ ?_)
      refine ⟨hx, ?_, hi.2.2⟩
      intro j hj1 hji
      by_contra hj
      have hjk : j ≤ k := le_trans (Nat.le_of_lt hji) hi.2.1
      have hij := Nat.find_min' hP ⟨hj1, hjk, hj⟩
      omega
  · rintro (hx | hx)
    · exact hx.1
    · simp only [mem_iUnion, exists_prop] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact hxi.1

/-- Nullity of the flat locus and every first-nonzero-jet locus aggregates to
nullity of the whole localized image. -/
theorem image_null_of_flatThrough_and_firstNonzeroJetLoci
    [MeasurableSpace F] (μ : Measure F) (f : E → F) (K : Set E) (k : ℕ)
    (hflat : μ (f '' SardHigherJetLocusDecompositionProbe.flatThrough f K k) = 0)
    (hjet : ∀ i ∈ Set.Icc 1 k, μ (f '' firstNonzeroJetLocus f K i) = 0) :
    μ (f '' K) = 0 := by
  rw [eq_flatThrough_union_iUnion_firstNonzeroJetLocus f K k, image_union]
  apply measure_union_null hflat
  rw [image_iUnion]
  apply measure_iUnion_null
  intro i
  rw [image_iUnion]
  exact measure_iUnion_null fun hi => hjet i hi

#print axioms eq_flatThrough_union_iUnion_firstNonzeroJetLocus
#print axioms image_null_of_flatThrough_and_firstNonzeroJetLoci
end SardFirstNonzeroJetLocusDecompositionProbe
