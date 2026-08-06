import Mathlib

/-!
# APM t91J02

## Statement repairs

None.

## Encoding questions

None. The torus is the actual product of two circles, the sphere is the unit
two-sphere in Euclidean `ℝ³`, and non-homeomorphism uses Mathlib's native
`Homeomorph` type.
-/

abbrev apm_t91J02_Torus := Circle × Circle
abbrev apm_t91J02_S2 :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem apm_t91j02 :
    ¬Nonempty (apm_t91J02_Torus ≃ₜ apm_t91J02_S2) := by
  sorry
