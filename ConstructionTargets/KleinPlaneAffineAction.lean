import ConstructionTargets.KleinCoordinateInversionPower

namespace KleinPlaneAffineAction

open KleinPresentedGroupCoordinateModel
open KleinPresentedGroupCoordinateNormalForm
open KleinCoordinateInversionPower

noncomputable def coordinateAct (c : Coordinates) (p : ℝ × ℝ) : ℝ × ℝ :=
  (((Multiplicative.toAdd c.1 : ℤ) : ℝ) +
      ((Multiplicative.toAdd (action c.2 (Multiplicative.ofAdd 1)) : ℤ) : ℝ) * p.1,
    ((Multiplicative.toAdd c.2 : ℤ) : ℝ) + p.2)

theorem coordinateAct_one (p : ℝ × ℝ) : coordinateAct 1 p = p := by
  ext <;> simp [coordinateAct]

theorem coordinateAct_mul (c d : Coordinates) (p : ℝ × ℝ) :
    coordinateAct (c * d) p = coordinateAct c (coordinateAct d p) := by
  ext
  · simp only [coordinateAct, SemidirectProduct.mul_left, SemidirectProduct.mul_right]
    rw [show Multiplicative.toAdd (c.1 * action c.2 d.1) =
        Multiplicative.toAdd c.1 + Multiplicative.toAdd (action c.2 d.1) by simp]
    rw [show action (c.2 * d.2) (Multiplicative.ofAdd 1) =
        action c.2 (action d.2 (Multiplicative.ofAdd 1)) by rw [map_mul]; rfl]
    rw [action_toAdd c.2 d.1,
      action_toAdd c.2 (action d.2 (Multiplicative.ofAdd 1))]
    norm_num
    ring
  · simp [coordinateAct]
    ring

noncomputable instance planeAction : MulAction PresentedKleinGroup (ℝ × ℝ) where
  smul g p := coordinateAct (coordinateEquiv g) p
  one_smul p := by
    change coordinateAct (coordinateEquiv 1) p = p
    rw [map_one, coordinateAct_one]
  mul_smul g h p := by
    change coordinateAct (coordinateEquiv (g * h)) p =
      coordinateAct (coordinateEquiv g) (coordinateAct (coordinateEquiv h) p)
    rw [map_mul, coordinateAct_mul]

@[simp] theorem generatorA_smul (p : ℝ × ℝ) :
    generatorA • p = (p.1 + 1, p.2) := by
  change coordinateAct (coordinateEquiv generatorA) p = _
  rw [coordinateEquiv_a]
  ext <;> simp [coordinateAct, A] <;> ring

@[simp] theorem generatorB_smul (p : ℝ × ℝ) :
    generatorB • p = (-p.1, p.2 + 1) := by
  change coordinateAct (coordinateEquiv generatorB) p = _
  rw [coordinateEquiv_b]
  ext <;> simp [coordinateAct, B] <;> ring

#print axioms coordinateAct_mul
#print axioms KleinPlaneAffineAction.planeAction

end KleinPlaneAffineAction
