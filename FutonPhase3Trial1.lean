import Mathlib

/-!
# Phase 3 Trial 1 — field_simp denominator-normalization lesson

This file exercises the lesson from memory `e-6bcbb51e`:
`field_simp` normalizes polynomial denominators into a canonical
factored form internally, and will NOT automatically use a nonzeroness
hypothesis unless it syntactically matches that internal form.

Here the denominator is the cubic `u^3 - 2*u^2 + 3`.  `field_simp`
normalizes it internally to `u^2 * (u - 2) + 3`.  A hypothesis
`hq : u^3 - 2*u^2 + 3 ≠ 0` does not match — the two are `ring`-equal but
not syntactically equal — so `field_simp [hq]` fails to clear the
resulting `(... )⁻¹` term.  The fix per the memory: rewrite the
hypothesis into the normalized form that `field_simp` actually uses
before calling it.

This differs from the Phase 2 trial (which used the quadratic
`u^2 - u + 1` and the goal `a⁻¹ * a = 1`): here we use a cubic
polynomial and the goal `a⁻¹ * a + u^2 = 1 + u^2`, requiring
`field_simp` to clear the inverse in the presence of an additive term.
-/

theorem phase3_field_simp_denom
    (u : ℝ) (hq : u^3 - 2*u^2 + 3 ≠ 0) :
    (u^3 - 2*u^2 + 3)⁻¹ * (u^3 - 2*u^2 + 3) + u^2 = 1 + u^2 := by
  -- field_simp normalizes the denominator u^3 - 2*u^2 + 3 internally
  -- to the factored form u^2 * (u - 2) + 3.  The hypothesis
  -- hq : u^3 - 2*u^2 + 3 ≠ 0 does not match, so field_simp [hq]
  -- cannot clear the inverse it creates.  Fix per memory e-6bcbb51e:
  -- rewrite hq into the form field_simp actually produces.
  rw [show u^3 - 2*u^2 + 3 = u^2 * (u - 2) + 3 from by ring] at hq
  -- field_simp now clears the inverse via the normalized hypothesis.
  field_simp [hq]
