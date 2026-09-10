import ConstructionTargets.PlaneArcEndpointTotalDifferenceRelativeSubmersion

noncomputable section
open Set
open scoped ContDiff

namespace PlaneArcEndpointInteriorCriticalLocusEmpty
open PlaneArcEndpointTotalCoincidenceSmooth
open PlaneArcEndpointTotalDifferenceRelativeSubmersion

abbrev Plane := ℝ × ℝ

def relativeInteriorDomain (U V : Set ℝ) : Set TotalParameters :=
  {p | p.1.1 ∈ U ∧ p.1.2 ∈ V ∧
    (p.1.1 ∈ Ioo (0 : ℝ) 1 ∨ p.1.2 ∈ Ioo (0 : ℝ) 1)}

def criticalLocus (a b : ℝ → Plane) : Set TotalParameters :=
  {p | ¬ Function.Surjective (fderiv ℝ (totalDifference a b) p)}

theorem relativeInteriorDomain_disjoint_criticalLocus
    (a b : ℝ → Plane) (U V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) :
    Disjoint (relativeInteriorDomain U V) (criticalLocus a b) := by
  rw [Set.disjoint_left]
  intro p hp hc
  exact hc (fderiv_totalDifference_surjective_on_interior_direction
    a b U V hU hV ha hb hp.1 hp.2.1 p.2.1 p.2.2 hp.2.2)

theorem relativeInteriorDomain_inter_criticalLocus_eq_empty
    (a b : ℝ → Plane) (U V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) :
    relativeInteriorDomain U V ∩ criticalLocus a b = ∅ :=
  Set.disjoint_iff_inter_eq_empty.mp
    (relativeInteriorDomain_disjoint_criticalLocus a b U V hU hV ha hb)

#print axioms relativeInteriorDomain_disjoint_criticalLocus
#print axioms relativeInteriorDomain_inter_criticalLocus_eq_empty

end PlaneArcEndpointInteriorCriticalLocusEmpty
