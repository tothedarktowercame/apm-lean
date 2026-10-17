# APM a95J03: Winding number of a trigonometric polynomial is bounded by its degree

## 1. Informal proof

**Why it's hard.** The curve $\gamma(t) = \sum_{n=-N}^N a(n)e^{int}$ is a trigonometric polynomial, and bounding its winding number by $N$ requires connecting the Fourier-analytic "degree" to the topological winding number — two very different notions. The winding number is an integral $(1/2\pi i)\oint dw/w$, while the degree $N$ is an algebraic property of the parametrisation.

**The key insight.** Substitute $w = e^{it}$, so $\gamma(t) = \sum a(n)w^n = P(w)/w^N$ where $P(w) = \sum a(n)w^{n+N}$ is a polynomial of degree $2N$. The winding number $\mathrm{Ind}(z; \gamma)$ equals the number of zeros of $\gamma(t) - z = 0$ counted with signs, which equals the number of roots of $P(w) - zw^N = 0$ on $|w| = 1$ counted with winding. Since $P(w) - zw^N$ is a polynomial of degree $\leq 2N$, it has at most $2N$ roots, and the winding number is bounded by $N$.

**Proof.**

*Step 1: Rewrite as a Laurent polynomial.* With $w = e^{it}$:

$\gamma(t) = \sum_{n=-N}^N a(n) w^n = w^{-N} \cdot \sum_{n=-N}^N a(n) w^{n+N} = w^{-N} \cdot P(w)$

where $P(w) = \sum_{k=0}^{2N} a(k-N) w^k$ is a polynomial of degree $\leq 2N$ (with $\deg P = 2N$ since $a(N) \neq 0$ or $a(-N) \neq 0$; at least one of the extreme coefficients is nonzero).

*Step 2: Winding number formula.* The winding number is:

$\mathrm{Ind}(z; \gamma) = (1/2\pi i) \oint_{|w|=1} \gamma'(t)/(\gamma(t) - z) \cdot dt$

Using $dt = dw/(iw)$:

$\mathrm{Ind}(z; \gamma) = (1/2\pi i) \oint_{|w|=1} d/dt[P(w)/w^N] / (P(w)/w^N - z) \cdot dw/(iw)$

This requires careful computation. More directly:

$\mathrm{Ind}(z; \gamma) = (1/2\pi i) \oint_{|w|=1} [d(\gamma)/(\gamma - z)]$

where $d(\gamma)$ is computed in terms of $dw$. Since $\gamma = P(w)w^{-N}$:

$d\gamma/dw = (P'(w)w^N - NP(w)w^{N-1})/w^{2N} = (P'(w) - NP(w)/w)/w^N$.

And $\gamma - z = (P(w) - zw^N)/w^N$.

So $d\gamma/(\gamma-z) = [P'(w) - NP(w)/w]/(P(w) - zw^N) \cdot dw = [wP'(w) - NP(w)]/[w(P(w) - zw^N)] \cdot dw$.

Thus: $\mathrm{Ind}(z; \gamma) = (1/2\pi i) \oint_{|w|=1} [wP'(w) - NP(w)] / [w(P(w) - zw^N)] dw$.

*Step 3: Relate to zeros of $Q(w) = P(w) - zw^N$.* $Q$ is a polynomial of degree $\leq 2N$. By the argument principle, the winding number of $\gamma$ around $z$ equals:

$\mathrm{Ind}(z; \gamma) = \#\{\text{zeros of } Q \text{ inside } |w|<1\} - N$

(The $-N$ comes from the $w^{-N}$ factor: the map $w \mapsto \gamma(w) = P(w)/w^N$ has a pole of order $N$ at $w = 0$, and by the argument principle for meromorphic functions, the winding number $= \#\text{zeros} - \#\text{poles}$ inside the contour.)

Since $Q$ has degree $\leq 2N$: $\#\{\text{zeros of } Q \text{ inside } |w|<1\} \leq 2N$ (total roots $\leq 2N$, all roots inside contributes at most $2N$). So $\mathrm{Ind}(z; \gamma) \leq 2N - N = N$.

Similarly $\#\{\text{zeros of } Q \text{ inside } |w|<1\} \geq 0$, so $\mathrm{Ind}(z; \gamma) \geq 0 - N = -N$.

Therefore **$-N \leq \mathrm{Ind}(z; \gamma) \leq N$**. ✓ ∎

**What connects.** This result connects Fourier analysis (the degree of a trigonometric polynomial) to topology (winding number). The substitution $w = e^{it}$ converts the circle parametrisation into an algebraic problem about polynomials, and the argument principle for meromorphic functions (zeros - poles = winding number) provides the bridge. The bound is sharp: $\gamma(t) = e^{iNt}$ has winding number $N$ around $0$. The result generalises: for a smooth closed curve with Fourier coefficients supported on $[-N, N]$, the winding number around any point is bounded by $N$. This is related to the Beurling-Helson theorem and the theory of analytic capacity.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv

open Complex Set

noncomputable section

/-- A trigonometric polynomial of degree N: γ(t) = Σ_{n=-N}^N a(n) e^{int}. -/
def trigPoly (a : ℤ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n in Finset.Icc (-(N : ℤ)) N, a n * exp (I * ↑n * ↑t)

/-- The winding number of γ about z. -/
def windingNumber (γ : ℝ → ℂ) (z : ℂ) : ℤ :=
  -- (1/2πi) ∫₀²π γ'(t)/(γ(t) - z) dt
  sorry

/-- Main theorem: -N ≤ Ind(z; γ) ≤ N. -/
theorem winding_number_bounded
    {a : ℤ → ℂ} {N : ℕ}
    (hN : a (-(N : ℤ)) ≠ 0 ∨ a (N : ℤ) ≠ 0)
    {z : ℂ} (hz : ∀ t ∈ Icc (0 : ℝ) (2 * π), trigPoly a N t ≠ z) :
    -(N : ℤ) ≤ windingNumber (trigPoly a N) z ∧
      windingNumber (trigPoly a N) z ≤ N := by
  sorry

/-- Upper bound: Ind ≤ N. -/
theorem winding_number_le
    {a : ℤ → ℂ} {N : ℕ}
    (hN : a (-(N : ℤ)) ≠ 0 ∨ a (N : ℤ) ≠ 0)
    {z : ℂ} (hz : ∀ t ∈ Icc (0 : ℝ) (2 * π), trigPoly a N t ≠ z) :
    windingNumber (trigPoly a N) z ≤ N := by
  sorry

/-- Lower bound: -N ≤ Ind. -/
theorem neg_le_winding_number
    {a : ℤ → ℂ} {N : ℕ}
    (hN : a (-(N : ℤ)) ≠ 0 ∨ a (N : ℤ) ≠ 0)
    {z : ℂ} (hz : ∀ t ∈ Icc (0 : ℝ) (2 * π), trigPoly a N t ≠ z) :
    -(N : ℤ) ≤ windingNumber (trigPoly a N) z := by
  sorry

/-- The algebraic polynomial P(w) = Σ a(k-N) w^k of degree ≤ 2N. -/
def algPoly (a : ℤ → ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ k in Finset.range (2 * N + 1), Polynomial.C (a (↑k - ↑N)) * Polynomial.X ^ k

/-- γ(t) = P(e^{it}) / e^{iNt} on the unit circle. -/
lemma trigPoly_eq_algPoly_div
    {a : ℤ → ℂ} {N : ℕ} (t : ℝ) :
    trigPoly a N t =
      Polynomial.aeval (exp (I * ↑t)) (algPoly a N) *
        exp (-(I * ↑N * ↑t)) := by
  sorry

/-- Argument principle: winding number = #zeros(Q) inside |w|<1 minus N,
    where Q(w) = P(w) - z w^N. -/
lemma winding_eq_zeros_minus_N
    {a : ℤ → ℂ} {N : ℕ} {z : ℂ}
    (hz : ∀ t ∈ Icc (0 : ℝ) (2 * π), trigPoly a N t ≠ z) :
    windingNumber (trigPoly a N) z =
      ((Polynomial.roots (algPoly a N - Polynomial.C z * Polynomial.X ^ N)).filter
        (fun w => ‖w‖ < 1)).card - N := by
  sorry

/-- Q has degree ≤ 2N, so at most 2N roots total. -/
lemma algPoly_sub_degree_le
    {a : ℤ → ℂ} {N : ℕ} {z : ℂ} :
    (algPoly a N - Polynomial.C z * Polynomial.X ^ N).natDegree ≤ 2 * N := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `Polynomial ℂ` / `ℂ[X]` — polynomials (for the algebraic reformulation)
- `Polynomial.roots` — multiset of roots
- `Polynomial.aeval` — polynomial evaluation
- `Polynomial.natDegree` — degree
- `Finset.Icc` — integer range $[-N, N]$
- `Complex.exp`, `Complex.I` — exponential and imaginary unit

**Key lemmas:**
- `Polynomial.card_roots_le_degree` — number of roots $\leq$ degree (the key bound: $Q$ has $\leq 2N$ roots)
- `Complex.exp_int_mul_two_pi_mul_I` — $e^{2\pi in} = 1$ (periodicity)
- `Polynomial.roots_mul` / `Polynomial.roots_sub` — roots of combined polynomials
- `Multiset.card_filter_le_card` — $\#\{\text{roots inside disk}\} \leq \#\{\text{all roots}\} \leq 2N$
- `Finset.sum_congr` — reindexing sums between trigonometric and algebraic forms
- `Complex.circleIntegral_sub_inv_of_mem_ball` — Cauchy integral / argument principle

**Tactic hints:**
- `rw [trigPoly_eq_algPoly_div]` — converting to the algebraic formulation
- `rw [winding_eq_zeros_minus_N hz]` — expressing winding as $\#\text{zeros} - N$
- `calc windingNumber ... = ... - N ≤ 2*N - N = N` — upper bound chain
- `omega` — for $2N - N = N$ and $0 - N = -N$ arithmetic
- `exact Multiset.card_filter_le_card _ _` — bounding filtered roots by total
- `exact Polynomial.card_roots_le_degree _` — bounding total roots by degree
- `simp [algPoly, trigPoly]` — unfolding definitions
- `ring` — for algebraic identity $P(w)/w^N$ manipulations