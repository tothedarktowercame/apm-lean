import ConstructionTargets.T94A08AffineCoordinatePatchRestrictedQuotient

open Set Topology
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace ConstructionTargets.T94A08ProjectiveConic

open ConstructionTargets.ComplexProjectiveChartTargets
open ConstructionTargets.ProjectiveSpaceTopology

def AffineCoordinatePatchTopology : Prop :=
  ∀ i : Fin 3,
    IsOpen {x : CP 2 | Projectivization.rep x i ≠ 0} ∧
    ContinuousOn (coordinates i)
      {x : CP 2 | Projectivization.rep x i ≠ 0}

theorem coordinates_quotientMap_eq_vectorRatio (i : Fin 3)
    (v : NonzeroVectors ℂ 2) (hv : v.1 i ≠ 0) :
    coordinates i (quotientMap ℂ 2 v) =
      fun j => v.1 j.1 / v.1 i := by
  funext j
  unfold coordinates
  have hm := Projectivization.mk_rep (quotientMap ℂ 2 v)
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _
    (Projectivization.rep_nonzero _) v.2).mp hm
  have hj := congrFun ha j.1
  have hi := congrFun ha i
  rw [← hj, ← hi]
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul]
  exact mul_div_mul_left _ _ (Units.ne_zero a)

theorem affineCoordinatePatchTopology : AffineCoordinatePatchTopology := by
  intro i
  rcases affineCoordinatePatchRestrictedQuotient i with ⟨f, hf, hquot⟩
  let A : Set (NonzeroVectors ℂ 2) := {v | v.1 i ≠ 0}
  let S : Set (CP 2) := {x | Projectivization.rep x i ≠ 0}
  have hAopen : IsOpen A := isOpen_ne.preimage
    ((continuous_apply i).comp continuous_subtype_val)
  have himage : (quotientMap ℂ 2) '' A = S := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (quotientMap_rep_coord_ne_zero_iff i v).2 hv
    · intro hx
      obtain ⟨v, rfl⟩ := (surjective_quotientMap ℂ 2) x
      exact ⟨v, (quotientMap_rep_coord_ne_zero_iff i v).1 hx, rfl⟩
  have hSopen : IsOpen S := by
    rw [← himage]
    exact projectiveQuotientOpenAuthority A hAopen
  refine ⟨hSopen, ?_⟩
  rw [continuousOn_iff_continuous_restrict]
  apply hquot.continuous_iff.mpr
  let ratio : {v : NonzeroVectors ℂ 2 // v.1 i ≠ 0} → AffineCoordinates i :=
    fun v j => v.1.1 j.1 / v.1.1 i
  have hratio : Continuous ratio := by
    apply continuous_pi
    intro j
    exact (((continuous_apply j.1).comp
      (continuous_subtype_val.comp continuous_subtype_val)).div
      ((continuous_apply i).comp
        (continuous_subtype_val.comp continuous_subtype_val))
      (fun v => v.2))
  convert hratio using 1
  funext v
  change coordinates i (f v).1 = ratio v
  rw [hf v]
  exact coordinates_quotientMap_eq_vectorRatio i v.1 v.2

end ConstructionTargets.T94A08ProjectiveConic
