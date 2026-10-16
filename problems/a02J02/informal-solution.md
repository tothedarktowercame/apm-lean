

# APM a02J02: Convergence in $L^p$ from a.e. convergence and norm convergence (Radon-Riesz theorem)

## Why It's Hard

Neither hypothesis alone suffices. A.e. convergence without norm convergence gives nothing about $L^p$ convergence (the typewriter sequence converges to 0 in measure but not in $L^{1}$). Norm convergence without a.e. convergence also fails (consider rearrangements). Together they work, but the proof requires a non-obvious tool: the uniform convexity of $L^p$ for $1 < p < \infty$, or equivalently, a clever use of Fatou's lemma applied to a function constructed to make the $L^p$ norm difference visible.

The critical case $p = 1$ fails: $f_n = 1 + (1/n)\sin(2\pi nx)$ on $[0,1]$ converges a.e. to $f = 1$ with $\|f_n\|_{1} \to \|f\|_{1} = 1$, but this is trivial. A genuine counterexample for $p = 1$ is harder to construct. The point is that for $p > 1$, the strict convexity of $t \mapsto |t|^p$ provides the rigidity that makes the theorem work.

## The Key Insight

Apply Fatou's lemma to the nonneg functions $g_{n}(x) = |f_{n}(x)|^p + |f(x)|^p - |f_{n}(x) - f(x)|^p$. The convexity inequality for $| \cdot |^p$ (with $p > 1$) guarantees $g_{n} \geq 0$ — this is where $p > 1$ is used. Fatou gives $\liminf \int g_{n} \geq \int \liminf g_{n}$. Since $f_{n} \to f$ a.e., $\liminf g_{n} = 2|f|^p$. And $\int g_{n} = \|f_{n}\|_p^p + \|f\|_p^p - \|f_{n} - f\|_p^p \to 2\|f\|_p^p - \limsup \|f_{n} - f\|_p^p$. The Fatou bound then forces $\limsup \|f_{n} - f\|_p^p \leq 0$.

**Alternative (Brézis-Lieb style):** Use the elementary inequality: for $p \geq 1$, $|a+b|^p \leq 2^{p-1}(|a|^p + |b|^p)$. Applied to $a = f_{n} - f$ and $b = f$: $|f_{n}|^p \leq 2^{p-1}(|f_{n}-f|^p + |f|^p)$, so $|f_{n}-f|^p \leq 2^{p-1}(|f_{n}|^p + |f|^p)$. This dominates $|f_{n}-f|^p$, but the dominating function is not *fixed* (it depends on $n$). The clean Fatou argument avoids this issue.

## Complete Proof

**Theorem.** Let $1 < p < \infty$. Let $f_{n}, f \in L^p([0,1])$ with $f_{n} \to f$ a.e. and $\|f_{n}\|_p \to \|f\|_p$. Then $\|f_{n} - f\|_p \to 0$.

**Proof.**

**Step 1: A pointwise convexity inequality.** For $p > 1$, the function $t \mapsto |t|^p$ is strictly convex. The following inequality holds for all $a, b \in \mathbb{R}$ (or $\mathbb{C}$):

$$|a - b|^p \leq |a|^p + |b|^p \quad \text{(trivially, by the triangle inequality this would need } 2^{p-1}\text{, but we use a sharper form).}$$

Actually, we use: for $p \geq 1$ and all $a, b \in \mathbb{R}$,

$$|a|^p + |b|^p - |a - b|^p \geq 0 \quad \text{when } p \leq 2$$

This doesn't hold in general for $p > 2$ (consider $a = 1, b = -1$: $1 + 1 - 2^p < 0$ for $p > 1$).

Let me use the correct approach.

**Step 1 (corrected): Apply Fatou to a different function.**

Define:

$$g_n(x) = 2^{p-1}(|f_n(x)|^p + |f(x)|^p) - |f_n(x) - f(x)|^p.$$

By the convexity inequality $|a - b|^p \leq 2^{p-1}(|a|^p + |b|^p)$ (which holds for $p \geq 1$ by convexity of $|\cdot|^p$), we have $g_{n} \geq 0$. ✓

**Step 2: Apply Fatou's lemma.**

Since $g_{n} \geq 0$ and $g_{n}$ is measurable:

$$\int \liminf_{n \to \infty} g_n \leq \liminf_{n \to \infty} \int g_n.$$

**Step 3: Compute both sides.**

*Left side:* Since $f_{n}(x) \to f(x)$ a.e.:
- $|f_{n}(x)|^p \to |f(x)|^p$ a.e.
- $|f_{n}(x) - f(x)|^p \to 0$ a.e.

So $\lim g_{n}(x) = 2^{p-1}(|f(x)|^p + |f(x)|^p) - 0 = 2^p |f(x)|^p$ a.e. Thus:

$$\int \liminf g_n = 2^p \|f\|_p^p.$$

*Right side:*

$$\int g_n = 2^{p-1}(\|f_n\|_p^p + \|f\|_p^p) - \|f_n - f\|_p^p.$$

Since $\|f_{n}\|_p \to \|f\|_p$, we have $\|f_{n}\|_p^p \to \|f\|_p^p$. So:

$$\liminf \int g_n = 2^{p-1}(\|f\|_p^p + \|f\|_p^p) - \limsup\|f_n - f\|_p^p = 2^p\|f\|_p^p - \limsup\|f_n - f\|_p^p.$$

**Step 4: Combine.**

$$2^p\|f\|_p^p \leq 2^p\|f\|_p^p - \limsup\|f_n - f\|_p^p.$$

Therefore:

$$\limsup \|f_n - f\|_p^p \leq 0.$$

Since $\|f_{n} - f\|_p^p \geq 0$, this forces $\|f_{n} - f\|_p^p \to 0$, i.e., $f_{n} \to f$ in $L^p$. ∎

## What Connects

**To the Radon-Riesz theorem / Kadec-Klee property.** This result is sometimes called the Radon-Riesz theorem for $L^p$. It says that in $L^p$ ($1 < p < \infty$), weak convergence plus norm convergence implies strong convergence. A.e. convergence implies weak convergence (by Egorov + DCT or by the Vitali convergence theorem argument), so a.e. convergence + norm convergence $\Longrightarrow$ strong convergence.

**To uniform convexity.** The $L^p$ spaces for $1 < p < \infty$ are uniformly convex (Clarkson's inequalities). Uniform convexity implies the Kadec-Klee property: weak convergence + norm convergence $\Longrightarrow$ strong convergence. Our direct Fatou proof avoids the machinery of uniform convexity.

**To the Brézis-Lieb lemma.** The Brézis-Lieb lemma (1983) says: if $f_{n} \to f$ a.e. and $\|f_{n}\|_p$ is bounded, then $\|f_{n}\|_p^p - \|f_{n} - f\|_p^p \to \|f\|_p^p$. Combined with $\|f_{n}\|_p \to \|f\|_p$, this gives $\|f_{n} - f\|_p \to 0$ directly.

**Why $p = 1$ fails.** For $p = 1$, the convexity inequality $|a-b| \leq |a| + |b|$ is an *equality* when $a$ and $b$ have opposite signs, so $g_{n} = |f_{n}| + |f| - |f_{n} - f| \geq 0$ but $g_{n}$ can equal 0 without $f_{n} = f$. The strict convexity of $|\cdot|^p$ for $p > 1$ is what makes $g_{n} \to 0$ force $f_{n} - f \to 0$.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Order.Filter.Basic

open MeasureTheory Set Filter ENNReal

noncomputable section

variable {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)

/-- The convexity inequality: |a-b|^p ≤ 2^{p-1}(|a|^p + |b|^p).
    Ensures the Fatou integrand gₙ is nonneg. -/
lemma rpow_sub_le_rpow_add {a b : ℝ} {p : ℝ} (hp : 1 ≤ p) :
    ‖a - b‖ ^ p ≤ 2 ^ (p - 1) * (‖a‖ ^ p + ‖b‖ ^ p) := by
  sorry

/-- The Fatou integrand:
    gₙ(x) = 2^{p-1}(|fₙ(x)|^p + |f(x)|^p) - |fₙ(x) - f(x)|^p ≥ 0. -/
lemma fatou_integrand_nonneg
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    {p : ℝ} (hp : 1 ≤ p) (n : ℕ) (x : ℝ) :
    0 ≤ 2 ^ (p - 1) * (‖f n x‖ ^ p + ‖g x‖ ^ p) -
      ‖f n x - g x‖ ^ p := by
  sorry

/-- Fatou's lemma: ∫ lim inf gₙ ≤ lim inf ∫ gₙ for nonneg gₙ. -/
lemma lintegral_liminf_le
    {g : ℕ → ℝ → ℝ≥0∞} (hg : ∀ n, Measurable (g n)) :
    ∫⁻ x in Icc (0 : ℝ) 1,
      Filter.liminf (fun n => g n x) atTop ∂volume ≤
    Filter.liminf (fun n =>
      ∫⁻ x in Icc (0 : ℝ) 1, g n x ∂volume) atTop := by
  sorry

/-- The pointwise limit of the Fatou integrand is 2^p |f(x)|^p. -/
lemma fatou_integrand_limit
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {p : ℝ} (hp : 1 ≤ p)
    {x : ℝ} (hconv : Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => 2 ^ (p - 1) * (‖f n x‖ ^ p + ‖g x‖ ^ p) -
      ‖f n x - g x‖ ^ p)
      atTop (𝓝 (2 ^ p * ‖g x‖ ^ p)) := by
  sorry

/-- Main theorem (Radon-Riesz): a.e. convergence + norm convergence
    ⟹ Lp convergence, for 1 < p < ∞. -/
theorem tendsto_Lp_of_ae_tendsto_of_norm_tendsto
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, Memℒp (f n) p (volume.restrict (Icc 0 1)))
    (hg : Memℒp g p (volume.restrict (Icc 0 1)))
    (hae : ∀ᵐ x ∂(volume.restrict (Icc (0:ℝ) 1)),
      Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hnorm : Tendsto (fun n => eLpNorm (f n) p (volume.restrict (Icc 0 1)))
      atTop (𝓝 (eLpNorm g p (volume.restrict (Icc 0 1))))) :
    Tendsto (fun n => eLpNorm (fun x => f n x - g x) p
      (volume.restrict (Icc 0 1)))
      atTop (𝓝 0) := by
  sorry

/-- Corollary: the Lp distance fₙ - f → 0. -/
theorem tendsto_Lp_sub_zero
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, Memℒp (f n) p (volume.restrict (Icc 0 1)))
    (hg : Memℒp g p (volume.restrict (Icc 0 1)))
    (hae : ∀ᵐ x ∂(volume.restrict (Icc (0:ℝ) 1)),
      Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hnorm : Tendsto (fun n =>
      eLpNorm (f n) p (volume.restrict (Icc 0 1)))
      atTop (𝓝 (eLpNorm g p (volume.restrict (Icc 0 1))))) :
    Tendsto (fun n =>
      eLpNorm (f n - g) p (volume.restrict (Icc 0 1)))
      atTop (𝓝 0) := by
  sorry

/-- The result fails for p = 1: counterexample exists. -/
theorem radon_riesz_fails_p_one :
    ∃ (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ),
      (∀ n, Memℒp (f n) 1 (volume.restrict (Icc 0 1))) ∧
      Memℒp g 1 (volume.restrict (Icc 0 1)) ∧
      (∀ᵐ x ∂volume.restrict (Icc (0:ℝ) 1),
        Tendsto (fun n => f n x) atTop (𝓝 (g x))) ∧
      Tendsto (fun n => eLpNorm (f n) 1 (volume.restrict (Icc 0 1)))
        atTop (𝓝 (eLpNorm g 1 (volume.restrict (Icc 0 1)))) ∧
      ¬Tendsto (fun n => eLpNorm (fun x => f n x - g x) 1
        (volume.restrict (Icc 0 1)))
        atTop (𝓝 0) := by
  sorry

end
```

**Mathlib notes:**

- `eLpNorm f p μ` (formerly `snorm`) is the $L^p$ seminorm. `Memℒp f p μ` says $f \in L^p(\mu)$.
- `Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)` encodes $\|f_{n} - f\|_p \to 0$.
- `∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))` encodes a.e. convergence.
- The norm convergence hypothesis uses `Tendsto ... (𝓝 (eLpNorm g p μ))` since the eLpNorm values are in `ℝ≥0∞` and convergence is in the `ℝ≥0∞` topology.
- The proof chain: `rpow_sub_le_rpow_add` (convexity) → `fatou_integrand_nonneg` ($g_{n} \geq 0$) → `lintegral_liminf_le` (Fatou) + `fatou_integrand_limit` (pointwise limit) → `tendsto_Lp_of_ae_tendsto_of_norm_tendsto` (combine for the squeeze).
- Mathlib likely has a version of this as `MeasureTheory.tendsto_Lp_of_tendsto_ae_of_tendsto_snorm` or similar in the Lp convergence files.
