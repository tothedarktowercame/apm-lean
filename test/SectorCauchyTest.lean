import ConstructionTargets.SectorCauchy

open Complex Real
open ConstructionTargets.SectorCauchy

noncomputable section

/-- The sector identity specializes nontrivially to the entire function
`z ↦ z`; this checks all three oriented boundary terms together. -/
example (R α : ℝ) :
    sectorBoundaryIntegral (fun z : ℂ => z) R α = 0 := by
  exact sectorBoundaryIntegral_eq_zero _ (by fun_prop) R α

/-- The local convex-domain theorem specializes to the whole plane. -/
example (R α : ℝ) :
    sectorBoundaryIntegral (fun z : ℂ => z) R α = 0 := by
  apply sectorBoundaryIntegral_eq_zero_of_convex
    (s := Set.univ) _ _ _ convex_univ isOpen_univ (by fun_prop)
  all_goals simp

#print axioms ConstructionTargets.SectorCauchy.sectorBoundaryIntegral_eq_zero
#print axioms ConstructionTargets.SectorCauchy.sectorBoundaryIntegral_eq_zero_of_convex
