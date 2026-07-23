

# APM a94A09: Unique fixed point of a disk self-map via Rouché

## 1. Informal proof

**Why it's hard.** The function f maps the closed disk into a region contained in the closed disk (|f| ≤ 1 on ∂Δ) but may not map the closed disk *strictly* into the open disk — the image could touch the boundary. The Brouwer fixed point theorem guarantees *at least one* fixed point, but we need *exactly one*, which requires a complex-analytic argument. Also, f maps ∂Δ into the closed disk (not necessarily into Δ), so f is not quite a strict self-map.

**The key insight.** Apply Rouché's theorem to compare z and f(z) on ∂Δ. Fixed points of f are zeros of g(z) = z - f(z). On ∂Δ: |z| = 1 and |f(z)| ≤ 1, but we also know z ≠ f(z) (no fixed points on ∂Δ). Rouché with the dominant term being z: |z| = 1 > |f(z)| or... this doesn't work directly since |f| could equal 1. Instead, use that |f(z)| ≤ 1 = |z| on ∂Δ and f(z) ≠ z on ∂Δ, then apply the argument principle directly to count zeros of z - f(z).

**Proof.**

*Step 1: Fixed points = zeros of g(z) = z - f(z).* The function g is continuous on Δ̄ and analytic on Δ. We count its zeros in Δ using the argument principle.

*Step 2: Rouché comparison.* On |z| = 1: |z| = 1 and |-f(z)| = |f(z)| ≤ 1. Write g(z) = z + (-f(z)). We want to apply Rouché with "big part" h(z) = z (which has exactly 1 zero in Δ) and "small part" -f(z).

Rouché requires |{-f(z)}| < |z| strictly on ∂Δ, i.e., |f(z)| < 1 on ∂Δ. But we only know |f(z)| ≤ 1.

*Step 3: Show |f(z)| < 1 on ∂Δ.* Suppose |f(z₀)| = 1 for some z₀ ∈ ∂Δ. Then f(z₀) ∈ ∂Δ. Consider: could f(z₀) = z₀? No — by hypothesis, f has no fixed points on ∂Δ. But we need |f(z₀)| < 1 (not just f(z₀) ≠ z₀) for Rouché. Actually, |f(z₀)| = 1 is possible with f(z₀) ≠ z₀.

*Alternative Step 3: Homotopy/winding number argument.* Consider the family h_t(z) = z - tf(z) for t ∈ [0,1]. On ∂Δ: h_t(z) = 0 iff z = tf(z), which means |z| = t|f(z)| ≤ t ≤ 1 with equality requiring t = 1 and |f(z)| = 1 and f(z) = z. For t < 1: |z| = 1 and t|f(z)| ≤ t < 1, so h_t ≠ 0 on ∂Δ. For t = 1: h₁(z) = z - f(z) ≠ 0 on ∂Δ by hypothesis. So h_t has no zeros on ∂Δ for any t ∈ [0,1].

The number of zeros of h_t in Δ is the winding number (1/2πi)∮_{∂Δ} h_t'/h_t dz, which is a continuous integer-valued function of t, hence constant. At t = 0: h₀(z) = z has exactly 1 zero in Δ. At t = 1: h₁(z) = z - f(z) has the same number of zeros = **1**. ∎

**What connects.** This combines the argument principle with a homotopy argument (deformation of the parameter t from 0 to 1). It's a complex-analytic proof of a Brouwer-type fixed point result with a uniqueness upgrade. The hypothesis "no fixed points on ∂Δ" is essential: without it, g = z - f(z) might have boundary zeros, invalidating the winding number argument. The same technique proves the Earle-Hamilton fixed point theorem: a holomorphic self-map of a bounded domain whose image is compactly contained has a unique fixed point.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.ContinuousOn

open Complex Metric Set Filter

noncomputable section

/-- Main theorem: f has exactly one fixed point in the open unit disk. -/
theorem unique_fixed_point_in_disk
    {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f (closedBall 0 1))
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_bdy : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hf_no_fix_bdy : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ z) :
    ∃! z₀ ∈ ball (0 : ℂ) 1, f z₀ = z₀ := by
  sorry

/-- Existence of at least one fixed point (Brouwer-type). -/
lemma exists_fixed_point_in_disk
    {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f (closedBall 0 1))
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_bdy : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hf_no_fix_bdy : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ z) :
    ∃ z₀ ∈ ball (0 : ℂ) 1, f z₀ = z₀ := by
  sorry

/-- The homotopy h_t(z) = z - t·f(z) has no zeros on ∂Δ for t ∈ [0,1]. -/
lemma homotopy_nonvanishing_on_boundary
    {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f (closedBall 0 1))
    (hf_bdy : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hf_no_fix_bdy : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ z)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ z ∈ sphere (0 : ℂ) 1, z - ↑t * f z ≠ 0 := by
  sorry

/-- The winding number of z - t·f(z) is constant in t, hence equals 1. -/
lemma winding_number_constant
    {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f (closedBall 0 1))
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_bdy : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hf_no_fix_bdy : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ z)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 / (2 * π * I)) * ∮ z in C(0, 1),
      deriv (fun w => w - ↑t * f w) z / (z - ↑t * f z) = 1 := by
  sorry

/-- g(z) = z - f(z) is analytic on Δ and has no zeros on ∂Δ. -/
lemma sub_fixed_analyticOn
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1)) :
    DifferentiableOn ℂ (fun z => z - f z) (ball 0 1) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `DifferentiableOn ℂ f (ball 0 1)` — holomorphicity on the open disk
- `ContinuousOn f (closedBall 0 1)` — continuity on the closed disk
- `Metric.sphere (0 : ℂ) 1` — the unit circle ∂Δ
- `Metric.ball (0 : ℂ) 1` — the open unit disk
- `Metric.closedBall (0 : ℂ) 1` — the closed unit disk
- `circleIntegral` / `∮ z in C(0,1)` — contour integral for the argument principle

**Key lemmas:**
- `Complex.circleIntegral_sub_inv_of_mem_ball` — Cauchy integral formula (for winding number computations)
- `DifferentiableOn.sub` — z - f(z) is analytic when f is
- `ContinuousOn.sub` — z - tf(z) is continuous when f is
- `Complex.norm_eq_abs` — ‖z‖ = |z| for circle membership
- `IsCompact.exists_forall_le` — continuous function on compact set attains bounds
- `Int.eq_of_continuous` / integer-valued continuous functions are constant — for the winding number homotopy invariance (may need to be stated manually)
- `Complex.circleIntegral_eq_zero_of_differentiableOn` — Cauchy's theorem

**Tactic hints:**
- `by_contra h; push_neg at h` — for showing h_t ≠ 0 on boundary
- `have : |t| * ‖f z‖ ≤ t ≤ 1 < |z|` — or handle the case t < 1 separately
- `rcases eq_or_lt_of_le (show t ≤ 1 from ht.2)` — case split t = 1 vs t < 1
- `calc ‖↑t * f z‖ = t * ‖f z‖ ≤ t * 1 = t < 1 = ‖z‖` — for t < 1 case
- `exact hf_no_fix_bdy z hz (by linarith ... )` — for t = 1 case
- `nlinarith [norm_nonneg (f z)]` — combining norm bounds
- `positivity` — for norm positivity
- `exact?` — finding the right Cauchy integral / winding number lemma