

# APM a95A05: Vanishing on a boundary arc implies identically zero

## 1. Informal proof

**Why it's hard.** f vanishes on the upper semicircle (an arc, not the entire boundary), so the maximum modulus principle doesn't immediately give f ≡ 0. The zero set on ∂Δ is a closed arc of positive length, but it's only half the boundary — f could be nonzero on the lower semicircle and in the interior.

**The key insight.** The upper semicircle is an arc containing infinitely many points, and an analytic function vanishing on a set with an accumulation point inside its domain of analyticity must vanish identically. But the arc is on the *boundary*, not the interior, so the identity theorem doesn't apply directly. Instead, use the Schwarz reflection principle or the fact that the zeros on ∂Δ have an accumulation point, and extend using the identity theorem for continuous boundary values.

Actually the cleanest approach: f vanishes on the upper semicircle, which is an arc containing infinitely many points (in fact, uncountably many). The function g(z) = f(z)·f(-z) is analytic on Δ and continuous on Δ̄. For z ∈ ∂Δ: if Im z ≥ 0, then f(z) = 0 so g(z) = 0; if Im z < 0, then -z has Im(-z) > 0, so f(-z) = 0 and g(z) = 0. So g = 0 on all of ∂Δ. By the maximum modulus principle, g ≡ 0 on Δ. Since Δ is connected and g = f · (f ∘ (-id)), either f ≡ 0 or f(-z) ≡ 0 on Δ. Either way, f ≡ 0.

Wait — "either f ≡ 0 or f(-z) ≡ 0" is the same conclusion (if f(-z) ≡ 0, substitute w = -z to get f ≡ 0 on Δ). But the deduction from f·h ≡ 0 to f ≡ 0 or h ≡ 0 requires the identity theorem for analytic functions on a connected domain (the zero set of an analytic function is discrete unless the function is identically zero). ✓

**Proof.**

Define g(z) = f(z) · f(-z). Then:
- g is analytic on Δ (product of analytic functions; -z ∈ Δ when z ∈ Δ).
- g is continuous on Δ̄ (product of continuous functions; -z ∈ Δ̄ when z ∈ Δ̄).

For z ∈ ∂Δ (|z| = 1):
- If Im z ≥ 0: f(z) = 0, so g(z) = 0.
- If Im z < 0: then Im(-z) = -Im z > 0 and |-z| = 1, so -z ∈ ∂Δ with Im(-z) ≥ 0, hence f(-z) = 0 and g(z) = 0.

So g = 0 on all of ∂Δ. By the maximum modulus principle (g is analytic on Δ, continuous on Δ̄, and |g| ≤ 0 on ∂Δ): g ≡ 0 on Δ.

So f(z) · f(-z) = 0 for all z ∈ Δ. The zero set of the analytic function f on Δ is either all of Δ or a discrete set. If f is not identically zero, its zero set Z_f is discrete. But then for z ∉ Z_f, we must have f(-z) = 0, so -z ∈ Z_f. This means Z_f and -Z_f partition the "nonzero region," and the complement Δ \ Z_f maps into Z_f under negation. But Z_f is discrete (countable, no accumulation points in Δ) while Δ \ Z_f is open and uncountable — so negation cannot map all of Δ \ Z_f into the discrete set Z_f. Contradiction. Therefore f ≡ 0 on Δ. ∎

**What connects.** This is an instance of the uniqueness principle for analytic functions: if f vanishes on a "large enough" subset of the boundary, then f vanishes identically. The upper semicircle is much more than needed — vanishing on any arc of positive length suffices (by the F. and M. Riesz theorem, or more elementarily by the identity theorem applied after Schwarz reflection). The g(z) = f(z)f(-z) trick avoids reflection entirely by reducing to the maximum principle on the full boundary. The result fails if f vanishes only at a single boundary point (e.g., f(z) = z - 1 vanishes at z = 1 but is not identically zero).

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex Metric Set

noncomputable section

/-- Main theorem: vanishing on the upper boundary arc forces f ≡ 0. -/
theorem eq_zero_of_vanishing_on_upper_arc
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_cont : ContinuousOn f (closedBall 0 1))
    (hf_vanish : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ z.im → f z = 0) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
  sorry

/-- The auxiliary function g(z) = f(z) · f(-z). -/
def auxProd (f : ℂ → ℂ) (z : ℂ) : ℂ := f z * f (-z)

/-- g is analytic on Δ. -/
lemma auxProd_differentiableOn
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) :
    DifferentiableOn ℂ (auxProd f) (ball 0 1) := by
  sorry

/-- g is continuous on Δ̄. -/
lemma auxProd_continuousOn
    {f : ℂ → ℂ} (hf : ContinuousOn f (closedBall 0 1)) :
    ContinuousOn (auxProd f) (closedBall 0 1) := by
  sorry

/-- g vanishes on all of ∂Δ. -/
lemma auxProd_vanish_on_boundary
    {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f (closedBall 0 1))
    (hf_vanish : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ z.im → f z = 0) :
    ∀ z ∈ sphere (0 : ℂ) 1, auxProd f z = 0 := by
  sorry

/-- Maximum principle: analytic on Δ, continuous on Δ̄,
    zero on ∂Δ ⟹ zero on Δ. -/
lemma eq_zero_of_boundary_zero
    {g : ℂ → ℂ}
    (hg_holo : DifferentiableOn ℂ g (ball 0 1))
    (hg_cont : ContinuousOn g (closedBall 0 1))
    (hg_bdy : ∀ z ∈ sphere (0 : ℂ) 1, g z = 0) :
    ∀ z ∈ closedBall (0 : ℂ) 1, g z = 0 := by
  sorry

/-- f(z)·f(-z) = 0 on a connected domain with f analytic ⟹ f ≡ 0. -/
lemma eq_zero_of_mul_neg_eq_zero
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (h : ∀ z ∈ ball (0 : ℂ) 1, f z * f (-z) = 0) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `DifferentiableOn ℂ f (ball 0 1)` — analyticity on the open disk
- `ContinuousOn f (closedBall 0 1)` — continuity on the closed disk
- `Metric.sphere (0 : ℂ) 1` — the unit circle ∂Δ
- `Complex.im` — imaginary part

**Key lemmas:**
- `Complex.norm_le_norm_of_forall_mem_frontier_le` — maximum modulus principle: if |g| ≤ M on ∂Δ and g is analytic on Δ, continuous on Δ̄, then |g| ≤ M on Δ. In `Mathlib.Analysis.Complex.AbsMax`
- `AnalyticAt.eq_zero_of_frequently_eq_zero` / `AnalyticOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero` — identity theorem: if f vanishes on a set with an accumulation point in a connected domain, f ≡ 0. In `Mathlib.Analysis.Analytic.IsolatedZeros`
- `DifferentiableOn.mul` — product of analytic functions is analytic
- `DifferentiableOn.comp` — composition (for f(-z))
- `ContinuousOn.mul` — product of continuous functions
- `differentiable_neg` — z ↦ -z is differentiable
- `neg_mem_ball_zero_iff` — -z ∈ ball 0 1 ↔ z ∈ ball 0 1
- `norm_neg` — ‖-z‖ = ‖z‖

**Tactic hints:**
- `have hg_zero := eq_zero_of_boundary_zero (auxProd_differentiableOn hf_holo) (auxProd_continuousOn hf_cont) (auxProd_vanish_on_boundary hf_cont hf_vanish)` — g ≡ 0 on Δ̄
- `rcases le_or_lt 0 z.im with h | h` — case split on Im z ≥ 0 vs Im z < 0 for the boundary
- `simp [auxProd, mul_eq_zero] at hg_zero` — extracting f(z) = 0 or f(-z) = 0
- `by_contra hf_ne` — assume f not identically zero for the discrete zeros argument
- `exact?` — finding the maximum principle or identity theorem
- `simp [norm_neg]` — for ‖-z‖ = ‖z‖ membership arguments
- `linarith` — for Im(-z) = -Im(z) > 0 when Im z < 0