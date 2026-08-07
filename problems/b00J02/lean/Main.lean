import Mathlib

/-!
# APM b00J02

## Statement repairs

None.

## Encoding questions

None. `GL (Fin 3) (ZMod 4)` is Mathlib's group of invertible `3 × 3`
matrices over `ℤ/4ℤ`.
-/

private noncomputable def b00j02UnitsEquivIsUnit (M : Type*) [Monoid M] :
    Mˣ ≃ {x : M // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.property.unit
  left_inv u := Units.ext (IsUnit.unit_spec u.isUnit)
  right_inv x := Subtype.ext x.property.unit_spec

theorem apm_b00j02 :
    Fintype.card (GL (Fin 3) (ZMod 4)) = 86016 := by
  rw [Fintype.card_congr (b00j02UnitsEquivIsUnit
    (Matrix (Fin 3) (Fin 3) (ZMod 4)))]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight
    (fun A : Matrix (Fin 3) (Fin 3) (ZMod 4) => A.isUnit_iff_isUnit_det))]
  native_decide
