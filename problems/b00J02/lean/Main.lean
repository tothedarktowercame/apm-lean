import Mathlib

/-!
# APM b00J02

## Statement repairs

None.

## Encoding questions

None. `GL (Fin 3) (ZMod 4)` is Mathlib's group of invertible `3 × 3`
matrices over `ℤ/4ℤ`.
-/

theorem apm_b00j02 :
    Fintype.card (GL (Fin 3) (ZMod 4)) = 86016 := by
  sorry
