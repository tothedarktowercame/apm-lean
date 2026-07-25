/-
! # APM a95J02: Entire function with |f(z)| ≥ |z|^lam and f(1) = 1 must be z^n

f is entire, f(1) = 1, |f(z)| ≥ |z|^lam for all z ∈ ℂ. Then f(z) = z^n
where n = lam (and lam must be a positive integer).

## Proof strategy

1. f has no zeros for z ≠ 0 (since |f(z)| ≥ |z|^lam > 0).
2. f(0) = 0: if not, 1/f is entire and bounded (→0 at ∞), so constant = 0
   by Liouville, contradicting f(1) = 1.
3. Factor f(z) = z^n · g(z) with g entire, g(0) ≠ 0.
4. |g(z)| ≥ |z|^{lam-n}: if lam > n, 1/g bounded → g constant contradiction;
   if lam < n, |g(0)| ≥ ∞ contradiction; so lam = n.
5. With lam = n: |g(z)| ≥ 1, so 1/g bounded → g constant → g = 1 by f(1) = 1.
   Thus f(z) = z^n.

## Theory boundaries

- Liouville's theorem IS in Mathlib (`exists_const_forall_eq_of_bounded`).
- The factoring f(z) = z^n · g(z) from the zero order at 0 needs the
  analytic zero structure API.
- The key step (1/g bounded entire → constant) needs 1/g differentiable,
  which requires g ≠ 0 everywhere, which follows from the bound.

## Statement repair

The generated statement uses `‖z‖ ^ lam` for real lam. In Lean, `‖z‖ : ℝ` and
`^lam` uses `Real.rpow`. This is correct but requires `‖z‖ ≥ 0` for rpow
to be well-defined (which it is, being a norm). We keep the statement.
-/

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Basic

open Complex

noncomputable section

/-- f has no zeros except at the origin.

For z ≠ 0: |f(z)| ≥ |z|^lam > 0 (since |z| > 0 and lam > 0). -/
lemma zero_only_at_origin
    {f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam)
    (hbound : ∀ z : ℂ, ‖z‖ ^ lam ≤ ‖f z‖) :
    ∀ z : ℂ, z ≠ 0 → f z ≠ 0 := by
  intro z hz hzero
  -- |z|^lam ≤ |f(z)| = |0| = 0, but |z|^lam > 0 for z ≠ 0, contradiction.
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrpow_pos : 0 < ‖z‖ ^ lam := Real.rpow_pos_of_pos hnorm_pos lam
  have hfbound : ‖z‖ ^ lam ≤ ‖f z‖ := hbound z
  rw [hzero, norm_zero] at hfbound
  linarith

/-- f(0) = 0.

If f(0) ≠ 0, then f has no zeros (by zero_only_at_origin + f(0) ≠ 0),
so 1/f is entire. And |1/f(z)| ≤ 1/|z|^lam → 0 as |z| → ∞.
By Liouville, 1/f is constant = c. Since |1/f(z)| → 0, c = 0,
contradicting 1/f(1) = 1/f(1) = 1 (since f(1) = 1).

**Blocker:** This requires constructing 1/f as a differentiable function
and showing it's bounded, then applying Liouville. The construction of
1/f from f ≠ 0 everywhere is available via `Differentiable.inv`, and
Liouville is available, but the boundedness argument (1/|z|^lam → 0)
requires showing the range of 1/f is bounded — which needs the
rpow → 0 at ∞ limit. -/
lemma f_zero_eq_zero
    {f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam)
    (hf : Differentiable ℂ f)
    (hf1 : f 1 = 1)
    (hbound : ∀ z : ℂ, ‖z‖ ^ lam ≤ ‖f z‖) :
    f 0 = 0 := by
  sorry

/-- Main theorem: f(z) = z^n where n = lam (lam is a positive integer).

Combines: f(0) = 0 → factor out z^n → g bounded → Liouville → g = 1. -/
theorem entire_lower_bound_is_monomial
    {f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam)
    (hf : Differentiable ℂ f)
    (hf1 : f 1 = 1)
    (hbound : ∀ z : ℂ, ‖z‖ ^ lam ≤ ‖f z‖) :
    ∃ n : ℕ, 0 < n ∧ (lam = ↑n) ∧ ∀ z, f z = z ^ n := by
  sorry

end
