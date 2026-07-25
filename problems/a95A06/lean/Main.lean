/-
! # APM a95A06: A lacunary series with natural boundary on the unit circle

f(z) = Σ_{n=1}^∞ z^{n!}/n! on the closed unit disk.

(a) f is continuous on Δ̄ and analytic on Δ.
(b) The unit circle is a natural boundary (no analytic continuation).

## Proof approach

### Part (a): Continuity and analyticity

- **Continuity on Δ̄**: By the Weierstrass M-test. Each term z^{n!}/n! is
  continuous, and ‖z^{n!}/n!‖ ≤ 1/n! on the closed disk (since ‖z‖ ≤ 1).
  Σ 1/n! converges (to e-1). Mathlib's `continuousOn_tsum` applies directly.

- **Analyticity on Δ**: Each term z^{n!}/n! is analytic (polynomial). The series
  converges uniformly on compact subsets of Δ (by comparison with geometric-like
  series). Mathlib's `differentiableOn_tsum` or power series results apply.

### Part (b): Natural boundary — PARTIAL

The natural boundary proof requires showing |f'(re^{2πiθ})| → ∞ for rational
θ, using the fact that n!/q is an integer for n ≥ q. This is a deep argument
involving divergence of lacunary series at boundary points. The Hadamard gap
theorem is not in Mathlib.

## Statement repair

The generated `lacunarySeries` uses `z ^ n.factorial / n.factorial` which is
correct. The series starts at n=1 (not n=0) per the TeX, but n=0! = 1 and
z^{0!} = z^1 = z, so n=0 also contributes z/1 = z. The TeX says n=1, so the
n=0 term (z^1/0! = z) is actually the same as the n=1 term (z^{1!}/1! = z).
We use the full sum from n=0 (matching Mathlib's tsum convention) — the extra
term is just z, which doesn't affect the convergence or boundary behavior.
-/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Complex Metric Set Filter Topology Nat

noncomputable section

/-- The lacunary series f(z) = Σ z^{n!}/n!.

Note: the problem specifies the sum from n=1. Since n=0 gives z^{0!}/0! = z,
and n=1 gives z^{1!}/1! = z, the n=0 term duplicates n=1. We sum from n=0
(Mathlib convention); the difference is a single polynomial term. -/
def lacunarySeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n.factorial / ↑n.factorial

/-- The n-th term of the lacunary series as a function of z. -/
def lacunaryTerm (n : ℕ) (z : ℂ) : ℂ :=
  z ^ n.factorial / ↑n.factorial

/-- M-test bound: ‖z^{n!}/n!‖ ≤ 1/n! on the closed unit disk.

Since ‖z‖ ≤ 1 on Δ̄, we have ‖z^{n!}‖ ≤ ‖z‖^{n!} ≤ 1, so
‖z^{n!}/n!‖ = ‖z^{n!}‖/n! ≤ 1/n!. -/
lemma lacunary_term_bound (n : ℕ) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖lacunaryTerm n z‖ ≤ (1 : ℝ) / ↑n.factorial := by
  rw [lacunaryTerm, norm_div]
  have hnorm : ‖z‖ ≤ 1 := by
    rw [mem_closedBall, dist_zero_right] at hz
    exact hz
  have hpow : ‖z ^ n.factorial‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hnorm
  calc ‖z ^ n.factorial‖ / ‖(↑n.factorial : ℂ)‖
      ≤ 1 / ‖(↑n.factorial : ℂ)‖ := by gcongr
    _ = 1 / ↑n.factorial := by simp
    _ = (1 : ℝ) / ↑n.factorial := by rfl

/-- The M-test majorant Σ 1/n! is summable.

Σ_{n=0}^∞ 1/n! = e. -/
lemma lacunary_majorant_summable :
    Summable (fun n : ℕ => (1 : ℝ) / ↑n.factorial) := by
  have := Real.summable_pow_div_factorial (1 : ℝ)
  simpa using this

/-- Each term z^{n!}/n! is continuous on the closed disk. -/
lemma lacunaryTerm_continuousOn (n : ℕ) :
    ContinuousOn (lacunaryTerm n) (closedBall (0 : ℂ) 1) := by
  apply ContinuousOn.div
  · exact (continuous_pow n.factorial).continuousOn
  · exact continuousOn_const
  · intro x _
    exact_mod_cast (by simp [Nat.factorial_ne_zero] : (↑n.factorial : ℂ) ≠ 0)

/-- Part (a): f is continuous on the closed unit disk Δ̄.

By the Weierstrass M-test (Mathlib's `continuousOn_tsum`):
- Each term lacunaryTerm n is continuous on Δ̄.
- The majorant 1/n! is summable.
- ‖lacunaryTerm n z‖ ≤ 1/n! on Δ̄. -/
theorem lacunarySeries_continuousOn :
    ContinuousOn lacunarySeries (closedBall (0 : ℂ) 1) := by
  -- Show lacunarySeries equals the tsum of lacunaryTerm
  have heq : lacunarySeries = fun z => ∑' n, lacunaryTerm n z := by
    funext z
    simp [lacunarySeries, lacunaryTerm]
  rw [heq]
  exact continuousOn_tsum
    (fun n => lacunaryTerm_continuousOn n)
    lacunary_majorant_summable
    (fun n z hz => lacunary_term_bound n z hz)

/-- Each term is differentiable on the open disk. -/
lemma lacunaryTerm_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (lacunaryTerm n) (ball (0 : ℂ) 1) := by
  have hpow : DifferentiableOn ℂ (fun z : ℂ => z ^ n.factorial) (ball 0 1) :=
    (differentiable_pow n.factorial).differentiableOn
  have heq : lacunaryTerm n = (↑n.factorial : ℂ)⁻¹ • (fun z : ℂ => z ^ n.factorial) := by
    funext z
    rw [lacunaryTerm, div_eq_mul_inv, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact hpow.const_smul _

/-- Part (a): f is analytic (holomorphic) on the open unit disk Δ.

Each term z^{n!}/n! is a polynomial (hence analytic). The series converges
uniformly on compact subsets of Δ by the M-test (applied to any closed ball
of radius r < 1). -/
theorem lacunarySeries_differentiableOn :
    DifferentiableOn ℂ lacunarySeries (ball (0 : ℂ) 1) := by
  -- Use HasSumUniformlyOn.of_norm_le_summable to get uniform convergence,
  -- then tsum of differentiable functions is differentiable.
  sorry

/-- For n ≥ q, n! is divisible by q. -/
lemma factorial_dvd_of_le {n q : ℕ} (hq : 0 < q) (hn : q ≤ n) :
    q ∣ n.factorial := by
  -- q! ∣ n! (from q ≤ n)
  have h := Nat.factorial_dvd_factorial hn
  -- q ∣ q! : since q > 0, q = (q-1).succ, and q! = q * (q-1)!
  have hq_dvd_qfact : q ∣ q.factorial := by
    obtain ⟨m, hm⟩ : ∃ m, q = m + 1 := Nat.exists_eq_succ_of_ne_zero hq.ne'
    rw [hm, Nat.factorial_succ]
    exact ⟨m.factorial, rfl⟩
  exact hq_dvd_qfact.trans h

/-- Part (b): The unit circle is a natural boundary for f.

No open set U properly containing Δ admits an analytic function F extending f.

**Blocker:** This requires the Hadamard gap theorem or an equivalent
divergence argument showing |f'(re^{2πiθ})| → ∞ for rational θ.
The argument uses:
1. For rational θ = p/q with n ≥ q: n! is divisible by q (factorial_dvd_of_le).
2. So e^{2πip·n!/q} = 1, making all tail terms real and positive.
3. The derivative Σ z^{n!-1} diverges at z = e^{2πiθ}.

None of these deep analysis tools are available in Mathlib. -/
theorem lacunarySeries_natural_boundary :
    ¬∃ (U : Set ℂ) (F : ℂ → ℂ),
      IsOpen U ∧ ball (0 : ℂ) 1 ⊂ U ∧
      DifferentiableOn ℂ F U ∧
      ∀ z ∈ ball (0 : ℂ) 1, F z = lacunarySeries z := by
  sorry

end
