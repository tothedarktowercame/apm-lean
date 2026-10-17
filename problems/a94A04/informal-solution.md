

# APM a94A04: Orthogonality to all monomials implies zero a.e.

## 1. Informal proof

**Why it's hard.** The hypothesis gives $\int x^n f(x) dx = 0$ for all $n$, which says $f$ is orthogonal to all monomials. Concluding $f = 0$ a.e. requires knowing that the monomials span a dense subspace of $L^{2}([0,1])$ — a non-trivial completeness/density result.

**The key insight.** By linearity, $\int p(x)f(x) dx = 0$ for every polynomial $p$. By Weierstrass approximation, polynomials are uniformly dense in $C([0,1])$, hence dense in $L^{2}([0,1])$. So $f$ is orthogonal to a dense subspace, forcing $f = 0$.

**Proof.**

*Step 1: Orthogonality extends to polynomials.* Since $\int_{0}^{1} x^{n}f(x)dx = 0$ for all $n \geq 0$ and the integral is linear, $\int_{0}^{1} p(x)f(x)dx = 0$ for every polynomial $p$ (any linear combination of monomials).

*Step 2: Orthogonality extends to continuous functions.* Let $g \in C([0,1])$. By the Weierstrass approximation theorem, there exist polynomials $p_{k}$ with $p_{k} \to g$ uniformly on $[0,1]$. Then:

$|\int_{0}^{1} g(x)f(x)dx| = |\int_{0}^{1} (g(x)-p_{k}(x))f(x)dx| \leq ||g - p_{k}||_{\infty} \cdot ||f||_{1} \leq ||g - p_{k}||_{\infty} \cdot ||f||_{2} \to 0$.

So $\int_{0}^{1} g(x)f(x)dx = 0$ for all $g \in C([0,1])$.

*Step 3: Orthogonality extends to all of $L^{2}$.* $C([0,1])$ is dense in $L^{2}([0,1])$. For any $h \in L^{2}$, choose $g_{k} \in C([0,1])$ with $||h - g_{k}||_{2} \to 0$. Then:

$|\int_{0}^{1} h(x)f(x)dx| = |\int_{0}^{1} (h(x)-g_{k}(x))f(x)dx| \leq ||h - g_{k}||_{2} \cdot ||f||_{2} \to 0$

by Cauchy-Schwarz. So $\langle h, f \rangle = 0$ for all $h \in L^{2}$.

*Step 4: Conclude.* Taking $h = f$: $||f||_{2}^{2} = \langle f, f \rangle = 0$, so $f = 0$ a.e. ∎

**What connects.** This is a consequence of the completeness of the polynomial system in $L^{2}([0,1])$, which itself follows from the Stone-Weierstrass theorem. The result fails if we replace $[0,1]$ by $[0,\infty)$ (the moment problem: a function can be orthogonal to all $x^{n}$ without being zero if the moments don't determine the measure). The $L^{2}$ hypothesis is used for Cauchy-Schwarz in Step 3; with only $f \in L^{1}$, Steps 1-2 still give $\int gf = 0$ for all continuous $g$, and then a density argument in $L^{\infty}$ (the dual of $L^{1}$) gives the same conclusion. The result also connects to the Müntz-Szász theorem, which characterises which subsequences of monomials are complete in $C([0,1])$ or $L^{2}([0,1])$.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Filter InnerProductSpace

noncomputable section

/-- Main theorem: f ∈ L²([0,1]) orthogonal to all monomials is zero a.e. -/
theorem zero_of_orthogonal_to_monomials
    {f : ℝ → ℝ}
    (hf : Memℒp f 2 (volume.restrict (Icc 0 1)))
    (hfm : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    (horth : ∀ n : ℕ, ∫ x in Icc (0:ℝ) 1, x ^ n * f x ∂volume = 0) :
    f =ᵐ[volume.restrict (Icc 0 1)] 0 := by
  sorry

/-- Orthogonality extends to all polynomials by linearity. -/
lemma orthogonal_to_polynomials
    {f : ℝ → ℝ}
    (horth : ∀ n : ℕ, ∫ x in Icc (0:ℝ) 1, x ^ n * f x ∂volume = 0)
    (p : Polynomial ℝ) :
    ∫ x in Icc (0:ℝ) 1, Polynomial.eval x p * f x ∂volume = 0 := by
  sorry

/-- Weierstrass: polynomials are uniformly dense in C([0,1]). -/
lemma polynomial_dense_C01
    {g : C(Set.Icc (0:ℝ) 1, ℝ)} {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ,
      ∀ x ∈ Icc (0:ℝ) 1,
        |g ⟨x, ‹_›⟩ - Polynomial.eval x p| < ε := by
  sorry

/-- Orthogonality extends to continuous functions. -/
lemma orthogonal_to_continuous
    {f : ℝ → ℝ}
    (hf : Memℒp f 2 (volume.restrict (Icc 0 1)))
    (hfm : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    (horth : ∀ n : ℕ, ∫ x in Icc (0:ℝ) 1, x ^ n * f x ∂volume = 0)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1)) :
    ∫ x in Icc (0:ℝ) 1, g x * f x ∂volume = 0 := by
  sorry

/-- C([0,1]) is dense in L²([0,1]). -/
lemma continuous_dense_L2 :
    Dense {g : Lp ℝ 2 (volume.restrict (Icc (0:ℝ) 1)) |
      ∃ h : ℝ → ℝ, ContinuousOn h (Icc 0 1) ∧
        g = Memℒp.toLp h sorry} := by
  sorry

/-- Orthogonality to a dense subspace forces zero. -/
lemma eq_zero_of_inner_eq_zero_dense
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {v : H} (hv : ∀ w : H, ⟪v, w⟫_ℝ = 0) :
    v = 0 := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.Memℒp f 2 μ` — $f \in L^{2}(\mu)$
- `Polynomial ℝ` — real polynomials
- `Polynomial.eval` — polynomial evaluation
- `ContinuousOn g (Icc 0 1)` — continuous functions on $[0,1]$
- `C(X, ℝ)` — continuous function type (for Stone-Weierstrass)
- `MeasureTheory.Lp ℝ 2 μ` — the $L^{2}$ Hilbert space
- `InnerProductSpace ℝ` — inner product structure
- `Filter.EventuallyEq` / `=ᵐ[μ]` — a.e. equality

**Key lemmas:**
- `polynomialFunctions.starClosure_topologicalClosure_eq_top` / `Polynomial.aeval_continuousMap_eq_top` — Stone-Weierstrass: polynomial functions are dense in $C(X)$ for compact $X$. In `Mathlib.Topology.ContinuousFunction.StoneWeierstrass`
- `MeasureTheory.Lp.boundedContinuousFunction_dense` — continuous functions are dense in Lp. In `Mathlib.MeasureTheory.Function.LpSpace`
- `inner_self_eq_zero` — $\langle v, v \rangle = 0 \Longrightarrow v = 0$
- `MeasureTheory.integral_mul_left` — linearity of integral
- `MeasureTheory.integral_finset_sum` — integral commutes with finite sums (for polynomial linearity)
- `norm_integral_le_of_norm_le` — $|\int gf| \leq ||g||_{\infty} \cdot \int|f|$
- `MeasureTheory.integral_inner` / Cauchy-Schwarz in $L^{2}$ — $|\langle g,f \rangle| \leq ||g||_{2} ||f||_{2}$
- `Polynomial.eval_eq_sum` — $p(x) = \sum a_{n}x^{n}$ (for extending orthogonality from monomials to polynomials)
- `MeasureTheory.ae_eq_zero_of_forall_inner` — orthogonality to all elements implies zero (may not exist by this exact name)

**Tactic hints:**
- `apply Polynomial.induction_on' p` — induction on polynomial structure
- `simp [Polynomial.eval_add, Polynomial.eval_mul]` — distributing evaluation
- `calc |∫ g f| = |∫ (g-p) f| ≤ ...` — for the approximation chain
- `gcongr` — for bounding $||g-p_{k}||$ terms
- `linarith` — combining ε bounds
- `exact inner_self_eq_zero.mp ...` — concluding $f = 0$ from $\langle f,f \rangle = 0$
- `ext` — for equality in $L^{2}$
- `exact?` — finding Stone-Weierstrass and density lemmas