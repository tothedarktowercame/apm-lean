import ConstructionTargets.PlaneArcEndpointPairBoundaryDecomposition

open Set

namespace PlaneArcEndpointPairBoundaryFinite
open PlaneArcEndpointPairBoundaryDecomposition

abbrev Plane := ℝ × ℝ

def endpointSet : Set ℝ := {0, 1}

def nonInteriorBoundary : Set Plane :=
  (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩
    {p | p.1 ∉ Ioo (0 : ℝ) 1 ∧ p.2 ∉ Ioo (0 : ℝ) 1}

lemma endpointSet_finite : endpointSet.Finite := by
  simp [endpointSet]

lemma nonInteriorBoundary_subset :
    nonInteriorBoundary ⊆ endpointSet ×ˢ endpointSet := by
  rintro p ⟨⟨hp1, hp2⟩, hni1, hni2⟩
  exact ⟨by simpa [endpointSet] using endpoint_cases hp1 hni1,
    by simpa [endpointSet] using endpoint_cases hp2 hni2⟩

theorem nonInteriorBoundary_finite : nonInteriorBoundary.Finite :=
  (endpointSet_finite.prod endpointSet_finite).subset nonInteriorBoundary_subset

theorem finite_union_nonInteriorBoundary {s : Set Plane} (hs : s.Finite) :
    (s ∪ nonInteriorBoundary).Finite := hs.union nonInteriorBoundary_finite

#print axioms nonInteriorBoundary_subset
#print axioms nonInteriorBoundary_finite
#print axioms finite_union_nonInteriorBoundary

end PlaneArcEndpointPairBoundaryFinite
