import ConstructionTargets.KleinPresentedGroupCoordinateModel

namespace KleinPresentedGroupConjugation

open FreeGroup
open KleinPresentedGroupCoordinateModel

theorem presented_relation :
    generatorB⁻¹ * generatorA * generatorB * generatorA = 1 := by
  change PresentedGroup.mk relations
      ((FreeGroup.of true)⁻¹ * FreeGroup.of false * FreeGroup.of true * FreeGroup.of false) = 1
  exact PresentedGroup.one_of_mem (Set.mem_singleton _)

theorem conjugateA : generatorB⁻¹ * generatorA * generatorB = generatorA⁻¹ := by
  calc
    generatorB⁻¹ * generatorA * generatorB =
        (generatorB⁻¹ * generatorA * generatorB * generatorA) * generatorA⁻¹ := by group
    _ = generatorA⁻¹ := by rw [presented_relation, one_mul]

theorem conjugateAPow (m : ℤ) :
    generatorB⁻¹ * generatorA ^ m * generatorB = generatorA ^ (-m) := by
  calc
    generatorB⁻¹ * generatorA ^ m * generatorB =
        (generatorB⁻¹ * generatorA * generatorB) ^ m := by
          simpa using (conj_zpow (a := generatorB⁻¹) (b := generatorA) (i := m)).symm
    _ = (generatorA⁻¹) ^ m := by rw [conjugateA]
    _ = generatorA ^ (-m) := by simp

#print axioms presented_relation
#print axioms conjugateA
#print axioms conjugateAPow

end KleinPresentedGroupConjugation
