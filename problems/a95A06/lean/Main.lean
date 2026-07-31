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

### Part (b): Natural boundary — statement defect

The intended connected-domain statement follows from the Hadamard gap theorem.
As formalized below, however, `U` is allowed to have an extra disconnected
component outside the unit disk.  Extending the series by zero on that component
is a counterexample; `lacunarySeries_has_disconnected_extension` proves this
inside Lean.

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
import Mathlib.Analysis.Complex.LocallyUniformLimit

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
  change DifferentiableOn ℂ (fun z => ∑' n, lacunaryTerm n z) (ball (0 : ℂ) 1)
  apply differentiableOn_tsum_of_summable_norm lacunary_majorant_summable
    lacunaryTerm_differentiableOn isOpen_ball
  intro n z hz
  exact lacunary_term_bound n z (ball_subset_closedBall hz)

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

/-- The stated natural-boundary target admits a disconnected extension.

The extra ball is disjoint from the unit disk, so the extension can be defined
independently there.  A valid natural-boundary statement must require the
larger open set (or at least the relevant component) to cross the unit circle. -/
lemma lacunarySeries_has_disconnected_extension :
    ∃ (U : Set ℂ) (F : ℂ → ℂ),
      IsOpen U ∧ ball (0 : ℂ) 1 ⊂ U ∧
      DifferentiableOn ℂ F U ∧
      ∀ z ∈ ball (0 : ℂ) 1, F z = lacunarySeries z := by
  classical
  let V : Set ℂ := ball (3 : ℂ) 1
  let U : Set ℂ := ball (0 : ℂ) 1 ∪ V
  let F : ℂ → ℂ := fun z => if z ∈ ball (0 : ℂ) 1 then lacunarySeries z else 0
  have hdis : Disjoint (ball (0 : ℂ) 1) V := by
    apply ball_disjoint_ball
    norm_num [V, Complex.dist_eq]
  have hstrict : ball (0 : ℂ) 1 ⊂ U := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨subset_union_left, ?_⟩
    intro heq
    have h3U : (3 : ℂ) ∈ U := by
      exact Or.inr (mem_ball_self (by norm_num))
    have h3not : (3 : ℂ) ∉ ball (0 : ℂ) 1 := by
      simp [mem_ball]
    exact h3not (heq ▸ h3U)
  refine ⟨U, F, isOpen_ball.union isOpen_ball, hstrict, ?_, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · have hlocal : F =ᶠ[𝓝 z] lacunarySeries := by
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw
        change (if w ∈ ball (0 : ℂ) 1 then lacunarySeries w else 0) =
          lacunarySeries w
        rw [if_pos hw]
      exact ((hlocal.differentiableAt_iff).2
        ((lacunarySeries_differentiableOn z hz).differentiableAt
          (isOpen_ball.mem_nhds hz))).differentiableWithinAt
    · have hlocal : F =ᶠ[𝓝 z] (fun _ : ℂ => 0) := by
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw
        have hw_not : w ∉ ball (0 : ℂ) 1 := fun hw0 =>
          Set.disjoint_left.1 hdis hw0 (by simpa [V] using hw)
        change (if w ∈ ball (0 : ℂ) 1 then lacunarySeries w else 0) = 0
        rw [if_neg hw_not]
      exact ((hlocal.differentiableAt_iff).2
        (differentiableAt_const (c := (0 : ℂ)))).differentiableWithinAt
  · intro z hz
    change (if z ∈ ball (0 : ℂ) 1 then lacunarySeries z else 0) =
      lacunarySeries z
    rw [if_pos hz]

/-- Part (b): The unit circle is a natural boundary for f.

No open set U properly containing Δ admits an analytic function F extending f.

**Statement defect:** `lacunarySeries_has_disconnected_extension` proves the
negation of this target's conclusion. A repaired version must require `U` to be
connected, or require the component containing the unit disk to cross the unit
circle. Only after that repair does the Hadamard-gap argument apply:
1. For rational θ = p/q with n ≥ q: n! is divisible by q (factorial_dvd_of_le).
2. So e^{2πip·n!/q} = 1, making all tail terms real and positive.
3. The derivative Σ z^{n!-1} diverges at z = e^{2πiθ}.
-/
theorem lacunarySeries_natural_boundary :
    ¬∃ (U : Set ℂ) (F : ℂ → ℂ),
      IsOpen U ∧ ball (0 : ℂ) 1 ⊂ U ∧
      DifferentiableOn ℂ F U ∧
      ∀ z ∈ ball (0 : ℂ) 1, F z = lacunarySeries z := by
  sorry

end
