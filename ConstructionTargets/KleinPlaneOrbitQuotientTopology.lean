import ConstructionTargets.KleinOrbitQuotientHomeomorph

noncomputable section

namespace ConstructionTargets.KleinPlaneOrbitQuotient

open Set
open KleinPresentedGroupCoordinateModel
open KleinPresentedGroupCoordinateNormalForm
open KleinPlaneAffineAction
open KleinSquareEqvGenToCases
open KleinClosedSquareOrbitQuotientEquiv

abbrev quotientMap : ℝ × ℝ → Quotient orbitSetoid :=
  fun p => Quotient.mk orbitSetoid p

theorem continuous_smul (g : PresentedKleinGroup) :
    Continuous (fun p : ℝ × ℝ => g • p) := by
  change Continuous (fun p : ℝ × ℝ => coordinateAct (coordinateEquiv g) p)
  exact (continuous_const.add (continuous_const.mul continuous_fst)).prodMk
    (continuous_const.add continuous_snd)

theorem isOpen_image_smul (g : PresentedKleinGroup) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) : IsOpen ((fun p : ℝ × ℝ => g • p) '' U) := by
  have heq : (fun p : ℝ × ℝ => g • p) '' U =
      (fun p : ℝ × ℝ => g⁻¹ • p) ⁻¹' U := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa [← mul_smul] using hq
    · intro hp
      refine ⟨g⁻¹ • p, hp, ?_⟩
      simp [← mul_smul]
  rw [heq]
  exact hU.preimage (continuous_smul g⁻¹)

theorem quotient_preimage_image (U : Set (ℝ × ℝ)) :
    quotientMap ⁻¹' (quotientMap '' U) =
      ⋃ g : PresentedKleinGroup, (fun p : ℝ × ℝ => g • p) '' U := by
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    have horbit : SameOrbit q p :=
      Quotient.exact hqp
    rcases horbit with ⟨g, rfl⟩
    exact mem_iUnion.2 ⟨g, ⟨q, hq, rfl⟩⟩
  · intro hp
    rcases mem_iUnion.1 hp with ⟨g, q, hq, rfl⟩
    exact ⟨q, hq, Quotient.sound ⟨g, rfl⟩⟩

theorem quotientMap_isOpen : IsOpenMap quotientMap := by
  intro U hU
  rw [isOpen_coinduced]
  rw [quotient_preimage_image]
  exact isOpen_iUnion fun g => isOpen_image_smul g hU

#print axioms quotientMap_isOpen

end ConstructionTargets.KleinPlaneOrbitQuotient
