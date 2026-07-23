import Mathlib

theorem phase2_recall_relevant (u : ℝ) (hq : u^2 - u + 1 ≠ 0) :
    (1 - u + u^2)⁻¹ * (1 - u + u^2) = 1 := by
  -- Memory e-6bcbb51e lesson: field_simp normalizes u^2 - u + 1 to the
  -- canonical monomial order 1 - u + u^2, but will not clear the inverse
  -- unless the nonzeroness hypothesis matches that exact normalized form.
  -- The hypothesis hq is stated as u^2 - u + 1 ≠ 0, which ring sees as
  -- equal but field_simp does not unify automatically. Fix per the memory:
  -- rewrite hq into the normalized form so field_simp can discharge it.
  rw [show u^2 - u + 1 = 1 - u + u^2 from by ring] at hq
  field_simp [hq]

theorem phase2_recall_irrelevant (x : ℝ) :
    (x + 1)^2 = x^2 + 2*x + 1 := by
  ring
