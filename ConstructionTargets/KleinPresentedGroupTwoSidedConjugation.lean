import ConstructionTargets.KleinPresentedGroupConjugation

namespace KleinPresentedGroupTwoSidedConjugation

open KleinPresentedGroupCoordinateModel
open KleinPresentedGroupConjugation

theorem reverseConjugateA :
    generatorB * generatorA * generatorB⁻¹ = generatorA⁻¹ := by
  have hneg : generatorB⁻¹ * generatorA⁻¹ * generatorB = generatorA := by
    simpa using conjugateAPow (-1)
  have commute : generatorB * generatorA = generatorA⁻¹ * generatorB := by
    calc
      generatorB * generatorA = generatorB * (generatorB⁻¹ * generatorA⁻¹ * generatorB) := by
        rw [hneg]
      _ = generatorA⁻¹ * generatorB := by group
  calc
    generatorB * generatorA * generatorB⁻¹ =
        (generatorA⁻¹ * generatorB) * generatorB⁻¹ := by rw [commute]
    _ = generatorA⁻¹ := by group

theorem reverseConjugateAPow (m : ℤ) :
    generatorB * generatorA ^ m * generatorB⁻¹ = generatorA ^ (-m) := by
  calc
    generatorB * generatorA ^ m * generatorB⁻¹ =
        (generatorB * generatorA * generatorB⁻¹) ^ m := by
          simpa using (conj_zpow (a := generatorB) (b := generatorA) (i := m)).symm
    _ = (generatorA⁻¹) ^ m := by rw [reverseConjugateA]
    _ = generatorA ^ (-m) := by simp

#print axioms reverseConjugateA
#print axioms reverseConjugateAPow

end KleinPresentedGroupTwoSidedConjugation
