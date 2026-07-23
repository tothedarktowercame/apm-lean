import Mathlib

/-!
# Phase 3 Trial 3 — tactic-algebra interference (field_simp normalization)

Exercises the lesson from corrected memory `e-aa9c729b`: `field_simp`
normalizes polynomial denominators into an internal partially factored
form, and requires a syntactically matching nonzeroness hypothesis to
clear the resulting inverse. The exact normalized form is empirical and
version-sensitive — discover it by inspecting the residual goal.

**Preregistered memory-hook paraphrase test:**
The query "normalize a denominator before using field_simp" did NOT
surface `math-formalization/tactic-algebra-interference` in the top 5
lexical candidates — the paraphrase did not match the pattern's indexed
hotwords. The pattern was selected directly based on prior trial
knowledge. This is a retrieval coverage gap for paraphrased hooks.

This theorem is distinct from Trial 1 (`u³−2u²+3`, `a⁻¹·a+u²=1+u²`) and
Trial 2 (`2u²+5u−3`, `a⁻¹·(4u²+10u−6)=2`). Here: quartic `u⁴−3u²+7`
with a division-based scaling identity.
-/

theorem phase3_trial3_field_simp_quartic
    (u : ℝ) (hq : u^4 - 3*u^2 + 7 ≠ 0) :
    (3*u^4 - 9*u^2 + 21) / (u^4 - 3*u^2 + 7) = 3 := by
  -- field_simp normalizes u^4 - 3*u^2 + 7 internally to the partially
  -- factored form u^2 * (u^2 - 3) + 7.  The hypothesis hq does not match
  -- — they are ring-equal but not syntactically equal — so field_simp
  -- [hq] cannot clear the denominator.  Fix per e-aa9c729b: discover the
  -- actual form from the residual goal, then rewrite hq to match.
  rw [show u^4 - 3*u^2 + 7 = u^2 * (u^2 - 3) + 7 from by ring] at hq
  field_simp [hq]
  ring
