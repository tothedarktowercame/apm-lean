import ConstructionTargets.T94A08AffineChartInverseNormalization
import ConstructionTargets.T94A08AffineCoordinatePatchPreimageIdentification
import ConstructionTargets.ComplexProjectiveChartTargets

open Set Topology
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace ConstructionTargets.T94A08ProjectiveConic

open ConstructionTargets.ComplexProjectiveChartTargets
open ConstructionTargets.ProjectiveSpaceTopology

def AffineCoordinatePatchRestrictedQuotient : Prop :=
  ∀ i : Fin 3,
    ∃ f : {v : NonzeroVectors ℂ 2 // v.1 i ≠ 0} →
        {x : CP 2 // Projectivization.rep x i ≠ 0},
      (∀ v, (f v).1 = quotientMap ℂ 2 v.1) ∧ IsQuotientMap f

theorem affineCoordinatePatchRestrictedQuotient :
    AffineCoordinatePatchRestrictedQuotient := by
  intro i
  let A : Set (NonzeroVectors ℂ 2) := {v | v.1 i ≠ 0}
  let S : Set (CP 2) := {x | Projectivization.rep x i ≠ 0}
  have hAS : A = (quotientMap ℂ 2) ⁻¹' S := by
    ext v
    simpa [A, S] using (quotientMap_rep_coord_ne_zero_iff i v).symm
  have hAopen : IsOpen A := by
    exact isOpen_ne.preimage
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
  let e : A ≃ₜ (quotientMap ℂ 2) ⁻¹' S := Homeomorph.setCongr hAS
  let g := S.restrictPreimage (quotientMap ℂ 2)
  let f : A → S := fun v => g (e v)
  refine ⟨f, ?_, ?_⟩
  · intro v
    rfl
  · change IsQuotientMap (g ∘ e)
    exact (projectiveQuotientMap_isQuotientMap.restrictPreimage_isOpen hSopen).comp
      e.isQuotientMap

end ConstructionTargets.T94A08ProjectiveConic
