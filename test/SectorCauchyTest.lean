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
#print axioms ConstructionTargets.SectorCauchy.sectorBoundaryIntegral_sub_inv_eq_log_endpoints
#print axioms ConstructionTargets.SectorCauchy.sectorBoundaryIntegral_sub_inv_eq_two_pi_I
#print axioms ConstructionTargets.SectorCauchy.sectorBoundaryIntegral_sub_inv_eq_two_pi_I_of_split_arc

example (c : ℂ) (f : ℂ → ℂ) (R α : ℝ) :
    sectorBoundaryIntegral (fun z => c * f z) R α =
      c * sectorBoundaryIntegral f R α := by
  exact sectorBoundaryIntegral_const_mul c f R α

/-- The three-side integrability predicate is closed under the same linear
operations as the boundary integral. -/
example (R α : ℝ) :
    SectorBoundaryIntegrable (fun z : ℂ => 2 * z + z) R α := by
  have hz : SectorBoundaryIntegrable (fun z : ℂ => z) R α := by
    constructor
    · exact (by fun_prop : Continuous (fun x : ℝ => (x : ℂ))).intervalIntegrable _ _
    constructor
    · exact (by fun_prop : Continuous (fun θ : ℝ =>
        (R : ℂ) * Complex.exp (I * θ) *
          (I * R * Complex.exp (I * θ)))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun x : ℝ =>
        (x : ℂ) * Complex.exp (I * α))).intervalIntegrable _ _
  exact (hz.const_mul 2).add hz
