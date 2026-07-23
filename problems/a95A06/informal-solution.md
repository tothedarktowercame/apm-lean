

# APM a95A06: A lacunary series with natural boundary on the unit circle

## 1. Informal proof

**Why it's hard.** Part (a) is routine (uniform convergence), but part (b) requires showing the unit circle is a *natural boundary* — every point of ∂Δ is singular. This means proving that f cannot be analytically continued past *any* boundary point, not just one specific point. The lacunary structure of the exponents (n!) is what makes this work but requires a careful blowup argument.

**The key insight.** At every rational angle θ = p/q on the unit circle, the derivative f'(re^{2πiθ}) → ∞ as r → 1⁻. This is because for n ≥ q, the term z^{n!} at z = re^{2πip/q} satisfies (re^{2πip/q})^{n!} = r^{n!} (since n!/q is an integer for n ≥ q, making e^{2πipn!/q} = 1), so f' accumulates contributions r^{n!-1} that sum to ∞. Since the rationals are dense in [0,1], f has singular points dense on ∂Δ, so no analytic continuation past any arc is possible.

**Proof.**

**(a) f is continuous on Δ̄ and analytic on Δ.**

The radius of convergence of Σ z^{n!}/n! is 1: by the root test, lim sup |1/n!|^{1/n!} = lim sup (n!)^{-1/n!} = 1 (since (n!)^{1/n!} → 1... actually log(n!)/n! → 0 by Stirling, so (n!)^{1/n!} = e^{log(n!)/n!} → 1). So f is analytic on Δ.

For continuity on Δ̄: on |z| ≤ 1, |z^{n!}/n!| ≤ 1/n!, and Σ 1/n! = e - 1 < ∞. By the Weierstrass M-test, the series converges uniformly on Δ̄. Since each partial sum is continuous (polynomial), f is continuous on Δ̄. ✓

**(b) The unit circle is a natural boundary.**

f'(z) = Σ_{n=1}^∞ z^{n!-1} · n!/n! = Σ_{n=1}^∞ z^{n!-1}.

Wait — f'(z) = Σ (n!/n!) z^{n!-1} = Σ z^{n!-1}. Hmm, the derivative of z^{n!}/n! is (n!/n!) z^{n!-1} = z^{n!-1}. So f'(z) = Σ_{n=1}^∞ z^{n!-1}.

Let θ = p/q ∈ ℚ and z = re^{2πiθ} with 0 < r < 1. For n ≥ q: n! is divisible by q, so e^{2πiθ·(n!-1)} = e^{-2πip/q} (constant in n). Thus:

|f'(re^{2πiθ})| ≥ |Σ_{n≥q} (re^{2πiθ})^{n!-1}| - |Σ_{n<q} (re^{2πiθ})^{n!-1}|.

For n ≥ q: (re^{2πiθ})^{n!-1} = r^{n!-1} · e^{2πiθ(n!-1)} = r^{n!-1} · e^{-2πip/q} (all terms have the same argument). So:

|Σ_{n≥q} r^{n!-1} e^{-2πip/q}| = Σ_{n≥q} r^{n!-1} → ∞ as r → 1⁻

since each term → 1 and there are infinitely many terms. (More precisely: for any M, choose N with N > q + M; then for r close to 1, Σ_{n=q}^{q+M} r^{n!-1} > M/2.)

So |f'(re^{2πiθ})| → ∞ as r → 1⁻ for every rational θ.

If f had an analytic continuation to an open set U ⊃ Δ, then f would be analytic at some boundary point z₀ = e^{2πiθ₀}. Since analyticity is an open condition, f would be analytic at all nearby boundary points, including some with rational angle. But analytic at e^{2πiθ} implies f' is bounded near e^{2πiθ}, contradicting |f'| → ∞. So no analytic continuation is possible. ✓ ∎

**What connects.** This is a classic example of a *lacunary series* with the unit circle as a natural boundary. The Hadamard-Ostrowski gap theorem guarantees this: if the exponents n_k satisfy n_{k+1}/n_k ≥ λ > 1 (the Hadamard gap condition), then the circle of convergence is a natural boundary. Here n_k = k!, so n_{k+1}/n_k = k+1 → ∞, which satisfies the gap condition superabundantly. The function f is one of the simplest examples of an analytic function that "cannot be continued" — a phenomenon that seems paradoxical from the viewpoint of real analysis (where analytic continuation often works) but is generic in complex analysis (most power series have natural boundaries).

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

open Complex Metric Set Filter Topology Nat

noncomputable section

/-- The lacunary series f(z) = Σ z^{n!}/n!. -/
def lacunarySeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n.factorial / n.factorial

/-- (a) f is continuous on the closed unit disk. -/
theorem lacunarySeries_continuousOn :
    ContinuousOn lacunarySeries (closedBall 0 1) := by
  sorry

/-- (a) f is analytic on the open unit disk. -/
theorem lacunarySeries_differentiableOn :
    DifferentiableOn ℂ lacunarySeries (ball 0 1) := by
  sorry

/-- (b) The unit circle is a natural boundary:
    no analytic continuation past any boundary point. -/
theorem lacunarySeries_natural_boundary :
    ¬∃ (U : Set ℂ) (F : ℂ → ℂ),
      IsOpen U ∧ ball (0 : ℂ) 1 ⊂ U ∧ ball (0 : ℂ) 1 ≠ U ∧
      DifferentiableOn ℂ F U ∧
      ∀ z ∈ ball (0 : ℂ) 1, F z = lacunarySeries z := by
  sorry

/-- Uniform convergence on the closed disk (Weierstrass M-test). -/
lemma lacunarySeries_uniformly_convergent :
    UniformCauchySeqOn
      (fun N z => ∑ n in Finset.range N, z ^ n.factorial / ↑(n.factorial))
      atTop (closedBall (0 : ℂ) 1) := by
  sorry

/-- M-test bound: |z^{n!}/n!| ≤ 1/n! on |z| ≤ 1. -/
lemma lacunarySeries_term_bound (n : ℕ) (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖z ^ n.factorial / ↑(n.factorial)‖ ≤ 1 / ↑(n.factorial) := by
  sorry

/-- The derivative f'(z) = Σ z^{n!-1} blows up at rational angles.
    For θ = p/q rational: |f'(re^{2πiθ})| → ∞ as r → 1⁻. -/
lemma deriv_blowup_at_rational_angle
    {p q : ℕ} (hq : 0 < q) :
    Tendsto (fun r : ℝ =>
      ‖deriv lacunarySeries (↑r * exp (2 * π * I * ↑p / ↑q))‖)
      (𝓝[<] 1) atTop := by
  sorry

/-- For n ≥ q, n! is divisible by q. -/
lemma factorial_dvd_of_le {n q : ℕ} (hq : 0 < q) (hn : q ≤ n) :
    q ∣ n.factorial := by
  sorry

/-- The partial derivative sum Σ_{n≥q} r^{n!-1} → ∞ as r → 1⁻. -/
lemma partial_sum_diverges
    {q : ℕ} (hq : 0 < q) :
    Tendsto (fun r : ℝ => ∑' (n : ℕ), if q ≤ n then r ^ (n.factorial - 1) else 0)
      (𝓝[<] 1) atTop := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `tsum` — infinite series (for the power series definition)
- `DifferentiableOn ℂ f (ball 0 1)` — analyticity
- `ContinuousOn f (closedBall 0 1)` — continuity on closed disk
- `UniformCauchySeqOn` — uniform Cauchy criterion (for M-test)
- `Nat.factorial` — n!
- `Filter.𝓝[<] 1` — left-neighbourhood filter of 1 (for r → 1⁻)
- `Filter.atTop` — for divergence

**Key lemmas:**
- `summable_of_sum_le` / `Summable.of_norm_bounded` — Weierstrass M-test: Σ‖aₙ‖ < ∞ ⟹ uniform convergence. Key for part (a)
- `Real.summable_inv_nat_factorial` — Σ 1/n! converges (= e-1). The M-test majorant
- `tendstoUniformlyOn_of_summable` — uniform convergence from summable bounds
- `UniformCauchySeqOn.continuousOn_limit` — uniform limit of continuous functions is continuous
- `DifferentiableOn.tsum` — termwise differentiability of uniformly convergent series of analytic functions
- `norm_pow_le` — ‖z^n‖ ≤ ‖z‖^n (for the M-test bound)
- `Nat.factorial_dvd_factorial` — q | n! when q ≤ n
- `Complex.exp_int_mul_two_pi_mul_I` — e^{2πik} = 1 (for the rational angle periodicity)
- `tendsto_atTop_atTop` — divergence characterisation

**Tactic hints:**
- `apply tendstoUniformlyOn_of_summable` — for the M-test
- `refine Summable.of_norm_bounded (fun n => 1 / ↑(n !)) Real.summable_inv_nat_factorial ?_` — providing the majorant
- `simp [norm_div, norm_pow, Complex.norm_natCast]` — simplifying the M-test bound
- `norm_num [Nat.factorial]` — computing small factorials
- `omega` — for n! - 1 and q ≤ n arithmetic
- `by_contra h; obtain ⟨U, F, hU, hU_big, hU_ne, hF, hF_eq⟩ := h` — unpacking the continuation
- `have : ∃ θ ∈ ℚ, e^{2πiθ} ∈ U` — finding a rational angle in U (density of rationals)
- `exact absurd (deriv_blowup_at_rational_angle ...) (not_tendsto_atTop_of_bounded ...)` — contradiction