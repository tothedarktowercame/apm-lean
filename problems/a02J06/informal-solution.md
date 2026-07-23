

# APM a02J06: Iterated Schwarz lemma

## Why It's Hard

This is a strengthening of the classical Schwarz lemma. The standard Schwarz lemma says: if f : D → D is holomorphic with f(0) = 0, then |f(z)| ≤ |z|. Here we additionally have f'(0) = 0, meaning f vanishes to second order at the origin, and the conclusion sharpens to |f(z)| ≤ |z|². The difficulty is recognizing that the same argument (apply the maximum principle to f(z)/z^k) works with k = 2 instead of k = 1, and that the equality case characterizes rotations of z².

## The Key Insight

Define g(z) = f(z)/z² for z ≠ 0 and g(0) = f''(0)/2 (the removable singularity value, since f(0) = f'(0) = 0 means f has a zero of order ≥ 2). Then g is holomorphic on D, and |g(z)| ≤ 1/r² on |z| = r for any r < 1 (since |f| ≤ 1). Letting r → 1 gives |g(z)| ≤ 1 on all of D, i.e., |f(z)| ≤ |z|². The bound at the origin gives |g(0)| = |f''(0)/2| ≤ 1, so |f''(0)| ≤ 2. Equality at any point forces g to be constant by the maximum modulus principle.

## Complete Proof

**Theorem.** Let f : D → ℂ be holomorphic with |f(z)| ≤ 1 for all z ∈ D, f(0) = 0, and f'(0) = 0. Then:

1. |f(z)| ≤ |z|² for all z ∈ D.
2. |f''(0)| ≤ 2.
3. If |f(w)| = |w|² for some w ∈ D \ {0}, then f(z) = βz² for some |β| = 1.

**Proof.**

**Step 1: Define g and show it is holomorphic on D.**

Since f(0) = 0 and f'(0) = 0, the Taylor expansion of f at 0 is f(z) = a₂z² + a₃z³ + ··· where a₂ = f''(0)/2. Define:

$$g(z) = \begin{cases} f(z)/z^2 & z \neq 0 \\ f''(0)/2 & z = 0. \end{cases}$$

Since f has a zero of order ≥ 2 at the origin, g is holomorphic on D (the singularity at 0 is removable: g(z) = a₂ + a₃z + a₄z² + ··· near 0).

**Step 2: Apply the maximum modulus principle to g.**

For 0 < r < 1, on the circle |z| = r:

$$|g(z)| = \frac{|f(z)|}{|z|^2} \leq \frac{1}{r^2}.$$

By the maximum modulus principle, |g(z)| ≤ 1/r² for all |z| ≤ r. Fix any z₀ ∈ D and choose any r with |z₀| < r < 1. Then |g(z₀)| ≤ 1/r². Letting r → 1⁻:

$$|g(z_0)| \leq 1.$$

Since z₀ was arbitrary, |g(z)| ≤ 1 for all z ∈ D.

**Step 3: Extract the conclusions.**

*Conclusion 1:* For z ∈ D: |f(z)| = |z²g(z)| = |z|² |g(z)| ≤ |z|² · 1 = |z|². ✓

*Conclusion 2:* |f''(0)/2| = |g(0)| ≤ 1, so |f''(0)| ≤ 2. ✓

**Step 4: Equality case.**

Suppose |f(w)| = |w|² for some w ∈ D \ {0}. Then |g(w)| = |f(w)|/|w|² = 1. Since |g| ≤ 1 on D and |g(w)| = 1 at an interior point w, the maximum modulus principle (applied to g on D) implies g is constant: g(z) = β for all z ∈ D, with |β| = |g(w)| = 1.

Therefore f(z) = z²g(z) = βz² for all z ∈ D. ✓ ∎

## What Connects

**To the Schwarz lemma.** The standard Schwarz lemma is the case where we only assume f(0) = 0 (one zero), giving |f(z)| ≤ |z|. This problem assumes f vanishes to order 2, giving |f(z)| ≤ |z|². The general pattern: if f vanishes to order k at the origin, then |f(z)| ≤ |z|^k, with equality iff f(z) = βz^k.

**To the Schwarz-Pick lemma.** The Schwarz-Pick lemma is the invariant version (for maps between hyperbolic disks). The iterated version here corresponds to maps that are "highly tangent" to the identity at a fixed point.

**To Cartan's uniqueness theorem.** For holomorphic self-maps of bounded domains fixing a point, if the derivative at the fixed point is the identity (or close to it), the map is increasingly constrained. The vanishing of f'(0) is a strong constraint that forces f to behave like z² at best.

**To the coefficient bounds in Schur's class.** The class of holomorphic functions f : D → D̄ is the Schur class. The bounds |a₁| ≤ 1 (Schwarz) and |a₂| ≤ 1 - |a₁|² (Schur) are classical. Here a₁ = f'(0) = 0, so |a₂| ≤ 1, giving |f''(0)| = 2|a₂| ≤ 2.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex Metric Set

noncomputable section

variable {f : ℂ → ℂ}

/-- The hypotheses: f holomorphic on D, bounded by 1, with f(0) = f'(0) = 0. -/
structure SchwarzOrder2 (f : ℂ → ℂ) : Prop where
  holo : DifferentiableOn ℂ f (ball 0 1)
  bound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1
  f_zero : f 0 = 0
  f'_zero : deriv f 0 = 0

/-- The auxiliary function g(z) = f(z)/z² with removable singularity. -/
def schwarzAux (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then iteratedDeriv 2 f 0 / 2 else f z / z ^ 2

/-- g is holomorphic on D (the singularity at 0 is removable). -/
lemma schwarzAux_differentiableOn (hf : SchwarzOrder2 f) :
    DifferentiableOn ℂ (schwarzAux f) (ball 0 1) := by
  sorry

/-- g(0) = f''(0)/2. -/
lemma schwarzAux_zero (hf : SchwarzOrder2 f) :
    schwarzAux f 0 = iteratedDeriv 2 f 0 / 2 := by
  sorry

/-- g equals f(z)/z² away from 0. -/
lemma schwarzAux_eq {z : ℂ} (hz : z ≠ 0) :
    schwarzAux f z = f z / z ^ 2 := by
  sorry

/-- Key bound: |g(z)| ≤ 1 on D, by the maximum modulus principle. -/
lemma schwarzAux_bound (hf : SchwarzOrder2 f) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖schwarzAux f z‖ ≤ 1 := by
  sorry

/-- Conclusion 1: |f(z)| ≤ |z|² for z ∈ D. -/
theorem schwarz_order2_bound (hf : SchwarzOrder2 f) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖ ^ 2 := by
  sorry

/-- Conclusion 2: |f''(0)| ≤ 2. -/
theorem schwarz_order2_second_deriv (hf : SchwarzOrder2 f) :
    ‖iteratedDeriv 2 f 0‖ ≤ 2 := by
  sorry

/-- Conclusion 3 (equality case): if |f(w)| = |w|² for some w ≠ 0 in D,
    then f(z) = βz² for some |β| = 1. -/
theorem schwarz_order2_equality (hf : SchwarzOrder2 f)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hw0 : w ≠ 0)
    (heq : ‖f w‖ = ‖w‖ ^ 2) :
    ∃ β : ℂ, ‖β‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, f z = β * z ^ 2 := by
  sorry

/-- The equality case follows from: g achieves its maximum at an interior
    point ⟹ g is constant (maximum modulus principle). -/
lemma schwarzAux_const_of_max (hf : SchwarzOrder2 f)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hw0 : w ≠ 0)
    (hmax : ‖schwarzAux f w‖ = 1) :
    ∃ β : ℂ, ‖β‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1,
      schwarzAux f z = β := by
  sorry

/-- General Schwarz lemma for vanishing of order k:
    if f(0) = f'(0) = ... = f^{(k-1)}(0) = 0, then |f(z)| ≤ |z|^k. -/
theorem schwarz_order_k
    {k : ℕ} (hk : 0 < k)
    (holo : DifferentiableOn ℂ f (ball 0 1))
    (bound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (vanish : ∀ j < k, iteratedDeriv j f 0 = 0) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖ ^ k := by
  sorry

end
```

**Mathlib notes:**

- `DifferentiableOn ℂ f (ball 0 1)` encodes holomorphicity on the open unit disk.
- `iteratedDeriv 2 f 0` is f''(0). The bound |f''(0)| ≤ 2 becomes `‖iteratedDeriv 2 f 0‖ ≤ 2`.
- `schwarzAux f z` is defined piecewise: f(z)/z² for z ≠ 0, f''(0)/2 for z = 0. The removable singularity theorem in Mathlib (`Complex.differentiableOn_update_of_bounded`) could be used to establish holomorphicity.
- The maximum modulus principle is in `Mathlib.Analysis.Complex.AbsMax` — the key lemma is something like `Complex.norm_eq_norm_of_isMaxOn` or `Complex.eqOn_of_isMaxOn_norm`.
- Mathlib also has `Complex.norm_le_norm_of_mapsTo_ball_self` (a version of the Schwarz lemma) in `Mathlib.Analysis.Complex.Schwarz`, which could serve as the basis for the order-k generalization.
- The general `schwarz_order_k` generalizes the result: vanishing to order k at the origin gives |f(z)| ≤ |z|^k with equality iff f = βz^k.
