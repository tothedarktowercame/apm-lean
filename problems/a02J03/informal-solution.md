

# APM a02J03: Rapid oscillation kills the integral — a generalized Riemann-Lebesgue lemma

## Why It's Hard

The function φ is *not* assumed to be periodic, not in any Lp space, and not bounded — only its averages over rectangles are controlled. As k → ∞, φ(kx) oscillates faster (or at least its averages over shrinking rectangles become small), and this should kill the integral against f ∈ L¹. But the proof requires showing that the rectangle-average bound on φ is enough to make ∫ φ(kx) g(x) dx small for simple functions g, and then extending to all of L¹ by density. The subtlety is that the bound M·m(Q)/(1+m(Q)) → 0 as m(Q) → 0, which is what provides the oscillation-type cancellation on small rectangles.

## The Key Insight

**For indicator functions of rectangles**, the integral ∫ φ(kx) 1\_Q(x) dx = k⁻ⁿ ∫\_{kQ} φ(y) dy, which by the hypothesis is bounded by M · m(kQ)/(1+m(kQ)) = M · kⁿm(Q)/(1+kⁿm(Q)). Dividing by m(Q): the "average" of φ(kx) over Q is bounded by Mkⁿ/(1+kⁿm(Q)), which → M/m(Q)... hmm, that doesn't go to zero.

Wait — let me re-examine. We have |∫\_{kQ} φ(y) dy| ≤ M · m(kQ)/(1+m(kQ)). So:

$$\left|\int_Q \varphi(kx)\,dx\right| = k^{-n}\left|\int_{kQ}\varphi(y)\,dy\right| \leq k^{-n} \cdot \frac{M \cdot k^n m(Q)}{1 + k^n m(Q)} = \frac{M \cdot m(Q)}{1 + k^n m(Q)}.$$

As k → ∞, this → 0 (for fixed Q with m(Q) > 0). So ∫\_Q φ(kx) dx → 0.

For f = c · 1\_Q: ∫ φ(kx) f(x) dx = c · ∫\_Q φ(kx) dx → 0. By linearity, this extends to simple functions (finite linear combinations of indicators of rectangles). Then by density of simple functions in L¹ and a uniform bound, it extends to all f ∈ L¹.

**But we need a uniform bound** on ∫ φ(kx) f(x) dx in terms of ||f||₁. The hypothesis gives |∫\_Q φ| ≤ M m(Q)/(1+m(Q)) ≤ M for all Q, which means φ has bounded averages — but this doesn't directly give ||φ||\_∞ ≤ M or anything like a pointwise bound. We need a different approach for the density argument.

The uniform bound comes from: |∫ φ(kx) f(x) dx| ≤ ... we need to bound this for general f ∈ L¹. The bound M·m(Q)/(1+m(Q)) ≤ M gives |∫\_Q φ(kx) dx| ≤ M·m(Q)/(1+kⁿm(Q)) ≤ M·k⁻ⁿ·(kⁿm(Q))/(1+kⁿm(Q)) ≤ M·k⁻ⁿ... no, that's ≤ M/kⁿ · kⁿm(Q) = Mm(Q). So |∫\_Q φ(kx) dx| ≤ M·m(Q). This means the functional f ↦ ∫ φ(kx) f(x) dx is bounded on L¹ with norm ≤ M (uniformly in k). This is the uniform bound we need.

## Complete Proof

**Theorem.** Let φ be measurable on ℝⁿ with |∫\_Q φ(x) dx| ≤ Mm(Q)/(1+m(Q)) for every rectangle Q. Let f ∈ L¹(ℝⁿ). Then ∫ φ(kx) f(x) dx → 0 as k → ∞.

**Proof.**

**Step 1: Verify ∫ φ(kx) f(x) dx is well-defined and uniformly bounded.**

For any rectangle Q:

$$\left|\int_Q \varphi(kx)\,dx\right| = k^{-n}\left|\int_{kQ}\varphi(y)\,dy\right| \leq k^{-n} \cdot \frac{M \cdot k^n m(Q)}{1+k^n m(Q)} = \frac{M \cdot m(Q)}{1 + k^n m(Q)} \leq M \cdot m(Q).$$

(Using the bound M·t/(1+t) ≤ M·t for t = kⁿm(Q) ≥ 0, and also M·t/(1+t) ≤ M.)

This means the linear functional Λ\_k(f) = ∫ φ(kx) f(x) dx, defined first on simple functions, satisfies |Λ\_k(1\_Q)| ≤ M · m(Q) = M · ||1\_Q||₁. By linearity, |Λ\_k(s)| ≤ M · ||s||₁ for any simple function s that is a linear combination of indicators of rectangles. By density and completeness, Λ\_k extends to a bounded linear functional on L¹ with ||Λ\_k|| ≤ M, uniformly in k. ✓

**Step 2: Vanishing on indicator functions of rectangles.**

For a fixed rectangle Q with m(Q) > 0:

$$|\Lambda_k(1_Q)| = \left|\int_Q \varphi(kx)\,dx\right| \leq \frac{M \cdot m(Q)}{1 + k^n m(Q)} \to 0 \quad \text{as } k \to \infty.$$

**Step 3: Vanishing on simple functions.**

By linearity, if s = Σᵢ cᵢ 1\_{Qᵢ} (finite sum, disjoint rectangles):

$$|\Lambda_k(s)| \leq \sum_i |c_i| \cdot |\Lambda_k(1_{Q_i})| \leq \sum_i |c_i| \cdot \frac{M \cdot m(Q_i)}{1+k^n m(Q_i)} \to 0.$$

**Step 4: Extension to all f ∈ L¹ by density.**

Fix ε > 0. Choose a simple function s (linear combination of indicators of rectangles) with ||f - s||₁ < ε/(2M). Then:

$$|\Lambda_k(f)| \leq |\Lambda_k(f - s)| + |\Lambda_k(s)| \leq M \cdot \|f - s\|_1 + |\Lambda_k(s)| < \frac{\varepsilon}{2} + |\Lambda_k(s)|.$$

By Step 3, |Λ\_k(s)| → 0, so for k large enough, |Λ\_k(s)| < ε/2. Therefore |Λ\_k(f)| < ε for all large k. Since ε was arbitrary, Λ\_k(f) → 0. ∎

## What Connects

**To the Riemann-Lebesgue lemma.** If φ(x) = e^{2πix·ξ₀}, then ∫ φ(kx)f(x) dx = f̂(kξ₀) → 0 by Riemann-Lebesgue. This problem generalises: φ doesn't need to be a character or even periodic — only the rectangle-average bound is needed. The bound Mm(Q)/(1+m(Q)) ensures that φ's averages over large sets are bounded by M (no blowup) and over small sets are small (cancellation), which is exactly the "oscillatory" behaviour that makes the integral vanish.

**To weak-* convergence.** The statement Λ\_k(f) → 0 for all f ∈ L¹ says that the sequence of functionals Λ\_k converges to 0 in the weak-* topology of L^∞ = (L¹)*. The uniform bound ||Λ\_k|| ≤ M and pointwise convergence on a dense set (simple functions) give weak-* convergence by the Banach-Steinhaus theorem.

**To mixing in ergodic theory.** In ergodic theory, a measure-preserving transformation is mixing if ∫ φ(T^n x) f(x) dx → (∫φ)(∫f). This problem is a continuous analogue: the dilation x ↦ kx "mixes" φ against f, and the rectangle-average bound plays the role of the mixing condition.

**To homogenisation.** In PDE homogenisation, one studies operators with rapidly oscillating coefficients a(x/ε) as ε → 0. The vanishing of ∫ a(x/ε) f(x) dx for non-constant parts of a is the cancellation mechanism that produces the homogenised (effective) equation.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open MeasureTheory Set Filter

noncomputable section

variable {n : ℕ}

/-- The rectangle-average bound on φ:
    |∫_Q φ| ≤ M · m(Q) / (1 + m(Q)) for all rectangles Q. -/
def RectAvgBound (φ : (Fin n → ℝ) → ℝ) (M : ℝ) : Prop :=
  ∀ (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
    ‖∫ x in Set.pi Set.univ (fun i => Icc (a i) (b i)), φ x ∂volume‖ ≤
      M * (volume (Set.pi Set.univ (fun i => Icc (a i) (b i)))).toReal /
        (1 + (volume (Set.pi Set.univ (fun i => Icc (a i) (b i)))).toReal)

/-- The dilated function φ(kx). -/
def dilate (φ : (Fin n → ℝ) → ℝ) (k : ℝ) (x : Fin n → ℝ) : ℝ :=
  φ (k • x)

/-- Step 1: uniform bound |∫ φ(kx) f(x) dx| ≤ M ‖f‖₁ for all k > 0. -/
lemma dilate_integral_le
    {φ : (Fin n → ℝ) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hφ : RectAvgBound φ M) (hφm : Measurable φ)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f volume)
    {k : ℝ} (hk : 0 < k) :
    ‖∫ x, dilate φ k x * f x ∂volume‖ ≤ M * ∫ x, ‖f x‖ ∂volume := by
  sorry

/-- Step 2: vanishing on indicator functions of rectangles.
    ∫_Q φ(kx) dx → 0 as k → ∞ for any fixed rectangle Q. -/
lemma dilate_integral_indicator_tendsto
    {φ : (Fin n → ℝ) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hφ : RectAvgBound φ M) (hφm : Measurable φ)
    {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    Tendsto (fun k : ℝ =>
      ∫ x in Set.pi Set.univ (fun i => Icc (a i) (b i)),
        dilate φ k x ∂volume)
      atTop (𝓝 0) := by
  sorry

/-- Step 3: vanishing on simple functions (finite linear combinations
    of indicators of rectangles). -/
lemma dilate_integral_simple_tendsto
    {φ : (Fin n → ℝ) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hφ : RectAvgBound φ M) (hφm : Measurable φ)
    {s : (Fin n → ℝ) → ℝ} (hs : Integrable s volume)
    (hs_simple : ∃ (rects : Finset ((Fin n → ℝ) × (Fin n → ℝ)))
                   (coeffs : (Fin n → ℝ) × (Fin n → ℝ) → ℝ),
      ∀ x, s x = ∑ r in rects, coeffs r *
        (Set.pi Set.univ (fun i => Icc (r.1 i) (r.2 i))).indicator (fun _ => (1:ℝ)) x) :
    Tendsto (fun k : ℝ => ∫ x, dilate φ k x * s x ∂volume)
      atTop (𝓝 0) := by
  sorry

/-- The key scaling identity: ∫_Q φ(kx) dx = k⁻ⁿ ∫_{kQ} φ(y) dy. -/
lemma dilate_integral_scaling
    {φ : (Fin n → ℝ) → ℝ} (hφm : Measurable φ)
    {Q : Set (Fin n → ℝ)} (hQ : MeasurableSet Q)
    {k : ℝ} (hk : 0 < k) :
    ∫ x in Q, dilate φ k x ∂volume =
      k ^ (-(n : ℤ)) • ∫ y in k • Q, φ y ∂volume := by
  sorry

/-- Main theorem: ∫ φ(kx) f(x) dx → 0 as k → ∞ for all f ∈ L¹. -/
theorem dilate_integral_tendsto_zero
    {φ : (Fin n → ℝ) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hφ : RectAvgBound φ M) (hφm : Measurable φ)
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f volume) :
    Tendsto (fun k : ℝ => ∫ x, dilate φ k x * f x ∂volume)
      atTop (𝓝 0) := by
  sorry

/-- Density: simple functions (indicator sums on rectangles)
    are dense in L¹. -/
lemma simple_rect_dense
    {f : (Fin n → ℝ) → ℝ} (hf : Integrable f volume) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : (Fin n → ℝ) → ℝ,
      Integrable s volume ∧
      (∃ (rects : Finset ((Fin n → ℝ) × (Fin n → ℝ)))
         (coeffs : (Fin n → ℝ) × (Fin n → ℝ) → ℝ),
        ∀ x, s x = ∑ r in rects, coeffs r *
          (Set.pi Set.univ (fun i => Icc (r.1 i) (r.2 i))).indicator
            (fun _ => (1:ℝ)) x) ∧
      ∫ x, ‖f x - s x‖ ∂volume < ε := by
  sorry

end
```

**Mathlib notes:**

- `Fin n → ℝ` is ℝⁿ; `volume` is the product Lebesgue measure. Rectangles are `Set.pi Set.univ (fun i => Icc (a i) (b i))`.
- `dilate φ k x = φ(k • x)` where `k • x` is the scalar multiplication in `Fin n → ℝ`.
- `RectAvgBound` encodes the hypothesis: the integral of φ over any rectangle Q satisfies |∫\_Q φ| ≤ M · m(Q)/(1+m(Q)).
- The scaling identity `dilate_integral_scaling` uses the change-of-variables y = kx, giving the factor k⁻ⁿ. `k • Q` is the dilation of the set.
- `Tendsto ... atTop (𝓝 0)` with the parameter `k : ℝ` encodes the limit as k → ∞ (along the `atTop` filter on ℝ).
- The density lemma `simple_rect_dense` states that finite linear combinations of rectangle indicators are dense in L¹(ℝⁿ). This is a standard measure theory fact.
- The proof chain: `dilate_integral_scaling` (change of variables) → `dilate_integral_indicator_tendsto` (vanishing on rectangles) → `dilate_integral_simple_tendsto` (linearity) → `dilate_integral_tendsto_zero` (density + uniform bound `dilate_integral_le`).
