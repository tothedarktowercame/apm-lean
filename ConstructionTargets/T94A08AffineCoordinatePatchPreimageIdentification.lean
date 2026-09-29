import ConstructionTargets.T94A08AffineChartInverseNormalization

open Set Topology
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace ConstructionTargets.T94A08ProjectiveConic

open ConstructionTargets.ComplexProjectiveChartTargets
open ConstructionTargets.ProjectiveSpaceTopology

theorem quotientMap_rep_coord_ne_zero_iff (i : Fin 3)
    (v : NonzeroVectors ℂ 2) :
    Projectivization.rep (quotientMap ℂ 2 v) i ≠ 0 ↔ v.1 i ≠ 0 := by
  have hm := Projectivization.mk_rep (quotientMap ℂ 2 v)
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _
    (Projectivization.rep_nonzero _) v.2).mp hm
  have hi := congrFun ha i
  constructor
  · intro hrep hv
    apply hrep
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul, hv, mul_zero]
      using hi.symm
  · intro hv hrep
    rw [hrep] at hi
    apply hv
    exact (mul_eq_zero.mp (by simpa only [Pi.smul_apply, Units.smul_def,
      smul_eq_mul] using hi)).resolve_left (Units.ne_zero a)

end ConstructionTargets.T94A08ProjectiveConic
