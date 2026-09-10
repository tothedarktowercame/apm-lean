import ConstructionTargets.PlaneArcEndpointPairParameterSurjectivity

open Set

namespace PlaneArcEndpointPairBoundaryDecomposition

lemma endpoint_cases {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hnot : t ∉ Ioo (0 : ℝ) 1) : t = 0 ∨ t = 1 := by
  rcases lt_or_eq_of_le ht.1 with hpos | rfl
  · rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact False.elim (hnot ⟨hpos, hlt⟩)
    · exact Or.inr heq
  · exact Or.inl rfl

theorem interior_direction_or_endpoint_pair {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    t ∈ Ioo (0 : ℝ) 1 ∨ s ∈ Ioo (0 : ℝ) 1 ∨
      (t = 0 ∧ s = 0) ∨ (t = 0 ∧ s = 1) ∨
      (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
  by_cases hit : t ∈ Ioo (0 : ℝ) 1
  · exact Or.inl hit
  by_cases his : s ∈ Ioo (0 : ℝ) 1
  · exact Or.inr (Or.inl his)
  rcases endpoint_cases ht hit with rfl | rfl <;>
    rcases endpoint_cases hs his with rfl | rfl <;> simp

#print axioms endpoint_cases
#print axioms interior_direction_or_endpoint_pair

end PlaneArcEndpointPairBoundaryDecomposition
