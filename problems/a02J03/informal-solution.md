

# APM a02J03: Rapid oscillation kills the integral — a generalized Riemann-Lebesgue lemma

## Why It's Hard

The function $\varphi$ is *not* assumed to be periodic, not in any Lp space, and not bounded — only its averages over rectangles are controlled. As $k \to \infty$, $\varphi(kx)$ oscillates faster (or at least its averages over shrinking rectangles become small), and this should kill the integral against $f \in L^{1}$. But the proof requires showing that the rectangle-average bound on $\varphi$ is enough to make $\int \varphi(kx) g(x)\, dx$ small for simple functions $g$, and then extending to all of $L^{1}$ by density. The subtlety is that the bound $M \cdot m(Q)/(1+m(Q)) \to 0$ as $m(Q) \to 0$, which is what provides the oscillation-type cancellation on small rectangles.

## The Key Insight

**For indicator functions of rectangles**, the integral $\int \varphi(kx) 1_Q(x)\, dx = k^{-n} \int_{kQ} \varphi(y)\, dy$, which by the hypothesis is bounded by $M \cdot m(kQ)/(1+m(kQ)) = M \cdot k^{n}m(Q)/(1+k^{n}m(Q))$. Dividing by $m(Q)$: the "average" of $\varphi(kx)$ over $Q$ is bounded by $Mk^{n}/(1+k^{n}m(Q))$, which $\to M/m(Q)$... hmm, that doesn't go to zero.

Wait — let me re-examine. We have $|\int_{kQ} \varphi(y)\, dy| \leq M \cdot m(kQ)/(1+m(kQ))$. So:

$$\left|\int_Q \varphi(kx)\,dx\right| = k^{-n}\left|\int_{kQ}\varphi(y)\,dy\right| \leq k^{-n} \cdot \frac{M \cdot k^n m(Q)}{1 + k^n m(Q)} = \frac{M \cdot m(Q)}{1 + k^n m(Q)}.$$

As $k \to \infty$, this $\to 0$ (for fixed $Q$ with $m(Q) > 0$). So $\int_Q \varphi(kx)\, dx \to 0$.

For $f = c \cdot 1_Q$: $\int \varphi(kx) f(x)\, dx = c \cdot \int_Q \varphi(kx)\, dx \to 0$. By linearity, this extends to simple functions (finite linear combinations of indicators of rectangles). Then by density of simple functions in $L^{1}$ and a uniform bound, it extends to all $f \in L^{1}$.

**But we need a uniform bound** on $\int \varphi(kx) f(x)\, dx$ in terms of $||f||_{1}$. The hypothesis gives $|\int_Q \varphi| \leq M m(Q)/(1+m(Q)) \leq M$ for all $Q$, which means $\varphi$ has bounded averages — but this doesn't directly give $||\varphi||_\infty \leq M$ or anything like a pointwise bound. We need a different approach for the density argument.

The uniform bound comes from: $|\int \varphi(kx) f(x)\, dx| \leq \ldots$ we need to bound this for general $f \in L^{1}$. The bound $M \cdot m(Q)/(1+m(Q)) \leq M$ gives $|\int_Q \varphi(kx)\, dx| \leq M \cdot m(Q)/(1+k^{n}m(Q)) \leq M \cdot k^{-n} \cdot (k^{n}m(Q))/(1+k^{n}m(Q)) \leq M \cdot k^{-n}\ldots$ no, that's $\leq M/k^{n} \cdot k^{n}m(Q) = Mm(Q)$. So $|\int_Q \varphi(kx)\, dx| \leq M \cdot m(Q)$. This means the functional $f \mapsto \int \varphi(kx) f(x)\, dx$ is bounded on $L^{1}$ with norm $\leq M$ (uniformly in $k$). This is the uniform bound we need.

## Complete Proof

**Theorem.** Let $\varphi$ be measurable on $\mathbb{R}^{n}$ with $|\int_Q \varphi(x)\, dx| \leq Mm(Q)/(1+m(Q))$ for every rectangle $Q$. Let $f \in L^{1}(\mathbb{R}^{n})$. Then $\int \varphi(kx) f(x)\, dx \to 0$ as $k \to \infty$.

**Proof.**

**Step 1: Verify $\int \varphi(kx) f(x)\, dx$ is well-defined and uniformly bounded.**

For any rectangle $Q$:

$$\left|\int_Q \varphi(kx)\,dx\right| = k^{-n}\left|\int_{kQ}\varphi(y)\,dy\right| \leq k^{-n} \cdot \frac{M \cdot k^n m(Q)}{1+k^n m(Q)} = \frac{M \cdot m(Q)}{1 + k^n m(Q)} \leq M \cdot m(Q).$$

(Using the bound $M \cdot t/(1+t) \leq M \cdot t$ for $t = k^{n}m(Q) \geq 0$, and also $M \cdot t/(1+t) \leq M$.)

This means the linear functional $\Lambda_k(f) = \int \varphi(kx) f(x)\, dx$, defined first on simple functions, satisfies $|\Lambda_k(1_Q)| \leq M \cdot m(Q) = M \cdot ||1_Q||_{1}$. By linearity, $|\Lambda_k(s)| \leq M \cdot ||s||_{1}$ for any simple function $s$ that is a linear combination of indicators of rectangles. By density and completeness, $\Lambda_k$ extends to a bounded linear functional on $L^{1}$ with $||\Lambda_k|| \leq M$, uniformly in $k$. ✓

**Step 2: Vanishing on indicator functions of rectangles.**

For a fixed rectangle $Q$ with $m(Q) > 0$:

$$|\Lambda_k(1_Q)| = \left|\int_Q \varphi(kx)\,dx\right| \leq \frac{M \cdot m(Q)}{1 + k^n m(Q)} \to 0 \quad \text{as } k \to \infty.$$

**Step 3: Vanishing on simple functions.**

By linearity, if $s = \sum_{i} c_{i} 1_{Q_{i}}$ (finite sum, disjoint rectangles):

$$|\Lambda_k(s)| \leq \sum_i |c_i| \cdot |\Lambda_k(1_{Q_i})| \leq \sum_i |c_i| \cdot \frac{M \cdot m(Q_i)}{1+k^n m(Q_i)} \to 0.$$

**Step 4: Extension to all $f \in L^{1}$ by density.**

Fix $\varepsilon > 0$. Choose a simple function $s$ (linear combination of indicators of rectangles) with $||f - s||_{1} < \varepsilon/(2M)$. Then:

$$|\Lambda_k(f)| \leq |\Lambda_k(f - s)| + |\Lambda_k(s)| \leq M \cdot \|f - s\|_1 + |\Lambda_k(s)| < \frac{\varepsilon}{2} + |\Lambda_k(s)|.$$

By Step 3, $|\Lambda_k(s)| \to 0$, so for $k$ large enough, $|\Lambda_k(s)| < \varepsilon/2$. Therefore $|\Lambda_k(f)| < \varepsilon$ for all large $k$. Since $\varepsilon$ was arbitrary, $\Lambda_k(f) \to 0$. ∎

## What Connects

**To the Riemann-Lebesgue lemma.** If $\varphi(x) = e^{2\pi ix \cdot \xi_{0}}$, then $\int \varphi(kx)f(x)\, dx = \hat{f}(k\xi_{0}) \to 0$ by Riemann-Lebesgue. This problem generalises: $\varphi$ doesn't need to be a character or even periodic — only the rectangle-average bound is needed. The bound $Mm(Q)/(1+m(Q))$ ensures that $\varphi$'s averages over large sets are bounded by $M$ (no blowup) and over small sets are small (cancellation), which is exactly the "oscillatory" behaviour that makes the integral vanish.

**To weak-* convergence.** The statement $\Lambda_k(f) \to 0$ for all $f \in L^{1}$ says that the sequence of functionals $\Lambda_k$ converges to 0 in the weak-* topology of $L^\infty = (L^{1})^*$. The uniform bound $||\Lambda_k|| \leq M$ and pointwise convergence on a dense set (simple functions) give weak-* convergence by the Banach-Steinhaus theorem.

**To mixing in ergodic theory.** In ergodic theory, a measure-preserving transformation is mixing if $\int \varphi(T^n x) f(x)\, dx \to (\int\varphi)(\int f)$. This problem is a continuous analogue: the dilation $x \mapsto kx$ "mixes" $\varphi$ against $f$, and the rectangle-average bound plays the role of the mixing condition.

**To homogenisation.** In PDE homogenisation, one studies operators with rapidly oscillating coefficients $a(x/\varepsilon)$ as $\varepsilon \to 0$. The vanishing of $\int a(x/\varepsilon) f(x)\, dx$ for non-constant parts of $a$ is the cancellation mechanism that produces the homogenised (effective) equation.

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

- `Fin n → ℝ` is $\mathbb{R}^{n}$; `volume` is the product Lebesgue measure. Rectangles are `Set.pi Set.univ (fun i => Icc (a i) (b i))`.
- `dilate φ k x = φ(k • x)` where `k • x` is the scalar multiplication in `Fin n → ℝ`.
- `RectAvgBound` encodes the hypothesis: the integral of $\varphi$ over any rectangle $Q$ satisfies $|\int_Q \varphi| \leq M \cdot m(Q)/(1+m(Q))$.
- The scaling identity `dilate_integral_scaling` uses the change-of-variables $y = kx$, giving the factor $k^{-n}$. `k • Q` is the dilation of the set.
- `Tendsto ... atTop (𝓝 0)` with the parameter `k : ℝ` encodes the limit as $k \to \infty$ (along the `atTop` filter on $\mathbb{R}$).
- The density lemma `simple_rect_dense` states that finite linear combinations of rectangle indicators are dense in $L^{1}(\mathbb{R}^{n})$. This is a standard measure theory fact.
- The proof chain: `dilate_integral_scaling` (change of variables) → `dilate_integral_indicator_tendsto` (vanishing on rectangles) → `dilate_integral_simple_tendsto` (linearity) → `dilate_integral_tendsto_zero` (density + uniform bound `dilate_integral_le`).
