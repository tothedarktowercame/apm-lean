import Mathlib

/-!
# Phase 3 Trial 2 — tactic-algebra interference (field_simp normalization)

Exercises the lesson that `field_simp` normalizes polynomial denominators
into an internal canonical form and will not use a nonzeroness hypothesis
unless it syntactically matches that form.

**Prediction error (kept explicit; original memory not silently rewritten):**
Memory `e-6bcbb51e` (now superseded by `e-aa9c729b`) claimed `field_simp`
normalizes to descending-power canonical monomial order (e.g. `1 - u + u²`).
Empirical testing shows `field_simp` produces a **partially factored** form:
here `2*u² + 5*u - 3` normalizes to `u * (2*u + 5) - 3`. The general lesson
from `e-9e32e848` — rewrite the hypothesis to match `field_simp`'s internal
form — remains correct; the specific normalized form must be discovered
empirically.

This theorem is distinct from Trial 1 (`u³ - 2u² + 3`, goal `a⁻¹·a + u² = 1 + u²`)
and from the earlier Trial 2 draft (`u³ + 3u - 5`, partial-fraction subtraction).
Here: quadratic `2u² + 5u - 3` with a scaling identity.
-/

theorem phase3_trial2_field_simp_quadratic
    (u : ℝ) (hq : 2*u^2 + 5*u - 3 ≠ 0) :
    (2*u^2 + 5*u - 3)⁻¹ * (4*u^2 + 10*u - 6) = 2 := by
  -- field_simp normalizes 2*u^2 + 5*u - 3 internally to u * (2*u + 5) - 3.
  -- The hypothesis hq does not match, so field_simp [hq] cannot clear
  -- the inverse.  Fix: rewrite hq to field_simp's internal factored form.
  rw [show 2*u^2 + 5*u - 3 = u * (2*u + 5) - 3 from by ring] at hq
  field_simp [hq]
  ring
