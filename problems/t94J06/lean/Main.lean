import Mathlib

/-!
# APM t94J06

## Statement repairs

None.

## Encoding questions

None.  The equation is stated directly over `ℂ`; its non-holomorphic real
term `cos ‖z‖` is explicitly coerced into `ℂ`.
-/

/-- The continuous, non-holomorphic function appearing in the problem. -/
noncomputable def apm_t94J06_function (z : ℂ) : ℂ :=
  z ^ 4 + 5 * z ^ 3 + Complex.I * z ^ 3 + ((Real.cos ‖z‖ : ℝ) : ℂ)

theorem apm_t94j06 :
    ∃ z : ℂ, apm_t94J06_function z = 0 := by
  sorry
