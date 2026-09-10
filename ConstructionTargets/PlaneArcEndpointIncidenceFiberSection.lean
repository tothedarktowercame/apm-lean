import ConstructionTargets.PlaneArcEndpointInteriorCriticalLocusEmpty

noncomputable section
open Set

namespace PlaneArcEndpointIncidenceFiberSection
open PlaneArcEndpointPreservingPerturbation
open PlaneArcEndpointPairParameterSurjectivity
open PlaneArcEndpointTotalCoincidenceSmooth
open PlaneArcEndpointInteriorCriticalLocusEmpty

abbrev Plane := ℝ × ℝ

def relativeCoincidenceFiber (a b : ℝ → Plane) (U V : Set ℝ)
    (va vb : Plane) : Set (ℝ × ℝ) :=
  {q | q.1 ∈ U ∧ q.2 ∈ V ∧
    (q.1 ∈ Ioo (0 : ℝ) 1 ∨ q.2 ∈ Ioo (0 : ℝ) 1) ∧
    pairDifference a b va vb q.1 q.2 = 0}

def incidenceZeroLocus (a b : ℝ → Plane) (U V : Set ℝ) : Set TotalParameters :=
  relativeInteriorDomain U V ∩ totalDifference a b ⁻¹' {0}

theorem mem_incidenceZeroLocus_section_iff (a b : ℝ → Plane) (U V : Set ℝ)
    (va vb : Plane) (q : ℝ × ℝ) :
    (q, (va, vb)) ∈ incidenceZeroLocus a b U V ↔
      q ∈ relativeCoincidenceFiber a b U V va vb := by
  simp only [incidenceZeroLocus, relativeInteriorDomain, relativeCoincidenceFiber,
    mem_inter_iff, mem_setOf_eq, mem_preimage, mem_singleton_iff]
  simp [totalDifference, pairDifference, and_assoc]

theorem relativeCoincidenceFiber_eq_incidence_section
    (a b : ℝ → Plane) (U V : Set ℝ) (va vb : Plane) :
    relativeCoincidenceFiber a b U V va vb =
      {q | (q, (va, vb)) ∈ incidenceZeroLocus a b U V} := by
  ext q
  exact (mem_incidenceZeroLocus_section_iff a b U V va vb q).symm

#print axioms mem_incidenceZeroLocus_section_iff
#print axioms relativeCoincidenceFiber_eq_incidence_section

end PlaneArcEndpointIncidenceFiberSection
