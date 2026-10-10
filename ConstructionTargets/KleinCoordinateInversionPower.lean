import ConstructionTargets.KleinPresentedGroupCoordinateNormalForm

namespace KleinCoordinateInversionPower

open KleinPresentedGroupCoordinateModel

theorem inversion_zpow_apply (n : ℤ) (z : ZMul) :
    Multiplicative.toAdd ((inversion ^ n) z) =
      Multiplicative.toAdd ((inversion ^ n) (Multiplicative.ofAdd 1)) *
        Multiplicative.toAdd z := by
  induction n using Int.induction_on generalizing z with
  | zero => simp
  | succ n ih =>
      rw [zpow_add_one inversion (n : ℤ)]
      simp only [MulAut.mul_apply]
      change Multiplicative.toAdd ((inversion ^ (n : ℤ)) z⁻¹) =
        Multiplicative.toAdd ((inversion ^ (n : ℤ)) (Multiplicative.ofAdd 1)⁻¹) *
          Multiplicative.toAdd z
      rw [ih (z := z⁻¹), ih (z := (Multiplicative.ofAdd 1)⁻¹)]
      simp
  | pred n ih =>
      rw [zpow_sub_one inversion (-(n : ℤ))]
      simp only [MulAut.mul_apply]
      change Multiplicative.toAdd ((inversion ^ (-(n : ℤ))) z⁻¹) =
        Multiplicative.toAdd ((inversion ^ (-(n : ℤ))) (Multiplicative.ofAdd 1)⁻¹) *
          Multiplicative.toAdd z
      rw [ih (z := z⁻¹), ih (z := (Multiplicative.ofAdd 1)⁻¹)]
      simp

theorem action_toAdd (g z : ZMul) :
    Multiplicative.toAdd (action g z) =
      Multiplicative.toAdd (action g (Multiplicative.ofAdd 1)) *
        Multiplicative.toAdd z := by
  exact inversion_zpow_apply _ _

#print axioms inversion_zpow_apply
#print axioms action_toAdd

end KleinCoordinateInversionPower
