import Mathlib

/-!
# APM t96J04 — no continuous surjection onto the irrationals

## Statement repairs

None.
-/

abbrev apm_t96j04_Irrational := {x : ℝ // Irrational x}

theorem apm_t96j04 :
    ¬ ∃ f : ℝ × ℚ → apm_t96j04_Irrational,
      Continuous f ∧ Function.Surjective f := by
  sorry
