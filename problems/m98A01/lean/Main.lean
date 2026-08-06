import Mathlib

/-!
# APM m98A01 — Banach/Hilbert foundations and closed graphs

## Statement repairs

None.

## Encoding note

Mathlib's structures `NormedSpace`, `CompleteSpace`, and `InnerProductSpace`
are the requested definitions. The example is the actual sup-norm space of
continuous functions on `[0,1]`, not a finite-dimensional surrogate.
-/

abbrev apm_m98a01_C01 := ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ

theorem apm_m98a01 :
    Nonempty (CompleteSpace apm_m98a01_C01) ∧
    (∃ f g : apm_m98a01_C01,
      ‖f + g‖ ^ 2 + ‖f - g‖ ^ 2 ≠ 2 * ‖f‖ ^ 2 + 2 * ‖g‖ ^ 2) ∧
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (T : X →L[ℝ] Y), Function.Surjective T → IsOpenMap T) ∧
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (T : X →ₗ[ℝ] Y),
      IsClosed {p : X × Y | p.2 = T p.1} → Continuous T) := by
  sorry
