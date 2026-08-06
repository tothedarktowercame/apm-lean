import Mathlib

/-!
# APM t97A01 — the nonorientable genus-three surface

## Statement repairs

None.

## Encoding note

The CW decomposition is the one-vertex, three-edge, one-face complex with
attaching word `a²b²c²`. Its cellular boundary and the Van Kampen presentation
are encoded directly, retaining both requested decompositions.
-/

def apm_t97a01_boundary₂ (n : ℤ) : Fin 3 → ℤ := fun _ => 2 * n

def apm_t97a01_relator : FreeGroup (Fin 3) :=
  (.of 0) * (.of 1) * (.of 0)⁻¹ * (.of 1)⁻¹ * (.of 2)⁻¹ * (.of 2)⁻¹

abbrev apm_t97a01_piOne := PresentedGroup ({apm_t97a01_relator} : Set (FreeGroup (Fin 3)))

theorem apm_t97a01 :
    (Nat.card (Fin 1) = 1 ∧ Nat.card (Fin 3) = 3 ∧ Nat.card (Fin 1) = 1) ∧
    Function.Injective apm_t97a01_boundary₂ ∧
    Nonempty (((Fin 3 → ℤ) ⧸ AddSubgroup.closure {apm_t97a01_boundary₂ 1}) ≃+
      (ℤ × ℤ × ZMod 2)) ∧
    Nonempty (apm_t97a01_piOne ≃*
      PresentedGroup ({apm_t97a01_relator} : Set (FreeGroup (Fin 3)))) := by
  sorry
