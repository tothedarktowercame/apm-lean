

# APM a94J08: No entire function satisfies |f(z)| ≥ |z|^{3/2}

## 1. Informal proof

**Why it's hard.** The bound |f(z)| ≥ |z|^{3/2} says f grows at least like |z|^{3/2}, which is faster than any polynomial of degree 1 but slower than degree 2. Since entire functions that grow polynomially must be polynomials (by the generalised Liouville theorem), and the exponent 3/2 is not an integer, there's a contradiction — but making this precise requires careful reasoning about why no polynomial (or transcendental function) can satisfy the lower bound.

**The key insight.** The bound |f(z)| ≥ |z|^{3/2} > 0 for z ≠ 0 means f has at most one zero (at z = 0). If f(0) = 0, the order of the zero is some integer n, so |f(z)| ~ c|z|ⁿ near 0. Then 1/f is entire away from 0 (and has a pole of order n at 0 if f vanishes there), and |1/f(z)| ≤ |z|^{-3/2} for z ≠ 0. This means g(z) = 1/f(z) has |g(z)| → 0 as |z| → ∞ and |g(z)| ≤ |z|^{-3/2} near 0. The singularity at 0 is removable or a pole, but |z|^{-3/2} is not the modulus of any meromorphic function near 0 — the exponent must be an integer.

**Proof.**

Suppose for contradiction that f is entire with |f(z)| ≥ |z|^{3/2} for all z ∈ ℂ.

*Step 1: f has a zero only at z = 0.* For z ≠ 0: |f(z)| ≥ |z|^{3/2} > 0, so f(z) ≠ 0. At z = 0: |f(0)| ≥ 0, so f(0) could be 0 or nonzero.

*Case A: f(0) ≠ 0.* Then f never vanishes, so 1/f is entire. And |1/f(z)| ≤ 1/|z|^{3/2} for z ≠ 0, so |1/f(z)| → 0 as |z| → ∞. By Liouville (a bounded entire function is constant), 1/f is constant, say 1/f ≡ c. Then f ≡ 1/c (constant). But then |f(z)| = |1/c| ≥ |z|^{3/2} for all z is impossible for large |z|. Contradiction.

*Case B: f(0) = 0.* Since f is entire and not identically zero, f has a zero of finite order n ≥ 1 at 0: f(z) = zⁿ h(z) where h is entire and h(0) ≠ 0. Then |zⁿ h(z)| ≥ |z|^{3/2}, so |h(z)| ≥ |z|^{3/2 - n} for z ≠ 0.

If n ≥ 2: |h(z)| ≥ |z|^{3/2-n} where 3/2 - n ≤ -1/2 < 0. So |h(z)| ≥ |z|^{-1/2} → ∞ as z → 0. But h is entire (hence continuous at 0), so |h(0)| = ∞ — impossible. Contradiction.

If n = 1: |h(z)| ≥ |z|^{1/2} for z ≠ 0. At z = 0: |h(0)| ≥ 0 (consistent). Now h is entire, h(0) ≠ 0, and |h(z)| ≥ |z|^{1/2}. Consider 1/h: it's entire (since h never vanishes: |h(z)| ≥ |z|^{1/2} > 0 for z ≠ 0, and h(0) ≠ 0). And |1/h(z)| ≤ |z|^{-1/2} → 0 as |z| → ∞. By Liouville, 1/h is constant, so h is constant. But |h(z)| ≥ |z|^{1/2} for all z contradicts h being constant (for large |z|). Contradiction. ✓ ∎

**What connects.** This is a consequence of the fact that entire functions of non-integer order cannot have |f| bounded below by a non-integer power of |z|. An entire function satisfying |f(z)| ≥ |z|^α for all z must be a polynomial of degree ≥ ⌈α⌉ (by the same argument), and a polynomial of degree n satisfies |f(z)| ~ c|z|ⁿ, which can match |z|^α only if α ≤ n (an integer). The exponent 3/2 being non-integer is what kills the construction. The result is related to the Hadamard factorisation theorem and the notion of order of an entire function: no entire function of order < 2 can avoid having zeros, and the distribution of zeros is constrained by the growth rate.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex

noncomputable section

/-- Main theorem: no entire function satisfies |f(z)| ≥ |z|^{3/2} for all z. -/
theorem no_entire_lower_bound_three_halves :
    ¬∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ z : ℂ, ‖z‖ ^ (3/2 : ℝ) ≤ ‖f z‖ := by
  sorry

/-- If f is entire and |f(z)| ≥ |z|^α for non-integer α > 0,
    then f cannot exist. General version. -/
theorem no_entire_lower_bound_noninteger
    {α : ℝ} (hα : 0 < α) (hα_nonint : ∀ n : ℤ, α ≠ ↑n) :
    ¬∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ z : ℂ, ‖z‖ ^ α ≤ ‖f z‖ := by
  sorry

/-- If entire f satisfies |f| ≥ |z|^α with α > 0,
    then f has at most one zero (at 0). -/
lemma at_most_one_zero_of_lower_bound
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {α : ℝ} (hα : 0 < α)
    (hbound : ∀ z : ℂ, ‖z‖ ^ α ≤ ‖f z‖) :
    ∀ z : ℂ, z ≠ 0 → f z ≠ 0 := by
  sorry

/-- 1/f is entire and bounded when f is entire, nonvanishing,
    with |f(z)| → ∞. -/
lemma inv_entire_bounded_of_lower_bound
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_ne : ∀ z, f z ≠ 0)
    {α : ℝ} (hα : 0 < α)
    (hbound : ∀ z, ‖z‖ ^ α ≤ ‖f z‖) :
    Differentiable ℂ (fun z => (f z)⁻¹) ∧
      ∃ M, ∀ z, ‖(f z)⁻¹‖ ≤ M := by
  sorry

/-- If f(0) = 0 with order n, then the factored function h
    satisfies |h(z)| ≥ |z|^{α-n}. -/
lemma factored_lower_bound
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {n : ℕ} (hn : 0 < n)
    (hfact : ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h 0 ≠ 0 ∧
      ∀ z, f z = z ^ n * h z)
    {α : ℝ} (hbound : ∀ z, ‖z‖ ^ α ≤ ‖f z‖) :
    ∀ z : ℂ, z ≠ 0 →
      ‖z‖ ^ (α - ↑n) ≤ ‖(Classical.choose hfact) z‖ := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `Differentiable ℂ f` — entire function
- `Real.rpow` — real power `‖z‖ ^ (3/2 : ℝ)` for non-integer exponents
- `AnalyticAt` — for analysing the order of a zero

**Key lemmas:**
- `Differentiable.apply_eq_apply_of_bounded` — Liouville's theorem: bounded entire function is constant. Key for the 1/f argument. In `Mathlib.Analysis.Complex.Liouville`
- `AnalyticAt.order_eq_nat_iff` — the order of a zero of an analytic function is a natural number. In `Mathlib.Analysis.Analytic.IsolatedZeros`
- `AnalyticAt.eq_pow_mul_of_order_eq` — f(z) = (z-a)ⁿ h(z) with h(a) ≠ 0
- `norm_inv` — ‖z⁻¹‖ = ‖z‖⁻¹
- `norm_pow` — ‖z^n‖ = ‖z‖^n
- `Real.rpow_natCast` — ‖z‖^(↑n) = ‖z‖^n
- `Differentiable.inv` — 1/f is differentiable where f ≠ 0
- `ContinuousAt.norm` — continuity of the norm (for contradiction at z = 0)
- `Real.rpow_lt_rpow` — monotonicity of rpow

**Tactic hints:**
- `by_contra h; push_neg at h; obtain ⟨f, hf_diff, hf_bound⟩ := h` — set up contradiction
- `by_cases hf0 : f 0 = 0` — case split on whether f vanishes at 0
- `have h_inv := Differentiable.apply_eq_apply_of_bounded ...` — apply Liouville to 1/f
- `have : ‖f z‖ = |c| for all z` — extract constant from Liouville conclusion
- `nlinarith [hf_bound z, Real.rpow_pos_of_pos (norm_pos_iff.mpr hz)]` — for the large-z contradiction
- `exact absurd (hfact.2.1) ...` — continuity contradiction at z = 0 when n ≥ 2
- `simp [norm_inv]` — for ‖1/f‖ = 1/‖f‖
- `positivity` — for ‖z‖^α > 0