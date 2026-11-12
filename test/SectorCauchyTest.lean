import ConstructionTargets.SectorCauchy

open Complex Real
open ConstructionTargets.SectorCauchy

noncomputable section

/-- The sector identity specializes nontrivially to the entire function
`z ↦ z`; this checks all three oriented boundary terms together. -/
example (R α : ℝ) :
    sectorBoundaryIntegral (fun z : ℂ => z) R α = 0 := by
  exact sectorBoundaryIntegral_eq_zero _ (by fun_prop) R α

#print axioms ConstructionTargets.SectorCauchy.sectorBoundaryIntegral_eq_zero
