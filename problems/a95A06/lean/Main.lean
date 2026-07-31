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
import Mathlib.RingTheory.RootsOfUnity.Complex

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

/-- The defining series is absolutely summable at every point of the closed
unit disk. -/
lemma summable_lacunaryTerm_of_mem_closedBall
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    Summable (fun n => lacunaryTerm n z) :=
  Summable.of_norm_bounded lacunary_majorant_summable
    (fun n => lacunary_term_bound n z hz)

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

/-- A connected proper open enlargement of the unit disk crosses its boundary.

This is the topological reduction needed before the analytic gap argument:
connectedness rules out jumping from the disk to the strict-superset witness
without attaining norm one. -/
lemma connected_superset_meets_unit_sphere
    {U : Set ℂ} (hconn : IsConnected U)
    (hstrict : ball (0 : ℂ) 1 ⊂ U) :
    ∃ z ∈ U, ‖z‖ = 1 := by
  have h0U : (0 : ℂ) ∈ U :=
    hstrict.le (mem_ball_self zero_lt_one)
  obtain ⟨w, hwU, hw_not_ball⟩ := Set.exists_of_ssubset hstrict
  have hw_norm : (1 : ℝ) ≤ ‖w‖ := by
    simpa [mem_ball, dist_zero_right, not_lt] using hw_not_ball
  have hone : (1 : ℝ) ∈ Set.Icc ‖(0 : ℂ)‖ ‖w‖ := by
    simp [hw_norm]
  obtain ⟨z, hzU, hz⟩ :=
    hconn.isPreconnected.intermediate_value h0U hwU
      continuous_norm.continuousOn hone
  exact ⟨z, hzU, hz⟩

/-- Every open set containing a point of the unit circle contains a root of
unity.  We parameterize the circle by real angle and use density of rational
angles. -/
lemma open_mem_unit_sphere_contains_rational_angle
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hzU : z ∈ U) (hz_norm : ‖z‖ = 1) :
    ∃ θ : ℚ, circleMap 0 1 (2 * Real.pi * (θ : ℝ)) ∈ U := by
  have hz_sphere : z ∈ sphere (0 : ℂ) 1 := by
    simpa [mem_sphere, dist_zero_right] using hz_norm
  have hrange : Set.range (circleMap 0 1) = sphere (0 : ℂ) 1 := by
    simpa only [abs_of_nonneg zero_le_one] using range_circleMap 0 1
  rw [← hrange] at hz_sphere
  obtain ⟨t, rfl⟩ := hz_sphere
  let circleParam : ℝ → ℂ := fun x => circleMap 0 1 (2 * Real.pi * x)
  have hcircleParam : Continuous circleParam :=
    (continuous_circleMap 0 1).comp
      (continuous_const.mul continuous_id)
  have ht : circleParam (t / (2 * Real.pi)) ∈ U := by
    have htwo_pi : (2 * Real.pi : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    have hang : 2 * Real.pi * (t / (2 * Real.pi)) = t := by
      exact mul_div_cancel₀ t htwo_pi
    simpa [circleParam, hang] using hzU
  obtain ⟨θ, hθ⟩ :=
    Rat.denseRange_cast.exists_mem_open
      (hU.preimage hcircleParam) ⟨t / (2 * Real.pi), ht⟩
  exact ⟨θ, hθ⟩

/-- At a rational angle, every sufficiently late factorial exponent kills the
angular part.  This is the arithmetic input to the Hadamard-gap argument. -/
lemma rational_angle_factorial_pow_eq_one
    (θ : ℚ) {n : ℕ} (hn : θ.den ≤ n) :
    circleMap 0 1 (2 * Real.pi * (θ : ℝ)) ^ n.factorial = 1 := by
  have hroot :
      IsPrimitiveRoot
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ))) θ.den :=
    Complex.isPrimitiveRoot_exp_rat θ
  have hpow :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (θ : ℂ)) ^ n.factorial = 1 :=
    (hroot.pow_eq_one_iff_dvd n.factorial).2
      (factorial_dvd_of_le θ.den_pos hn)
  convert hpow using 1
  simp [circleMap_zero]
  ring_nf

/-- Part (b): The unit circle is a natural boundary for f.

No connected open set U properly containing Δ admits an analytic function F
extending f. Connectedness excludes the disconnected extension exhibited by
`lacunarySeries_has_disconnected_extension`.

The Hadamard-gap argument applies:
1. For rational θ = p/q with n ≥ q: n! is divisible by q (factorial_dvd_of_le).
2. So e^{2πip·n!/q} = 1, making all tail terms real and positive.
3. The derivative Σ z^{n!-1} diverges at z = e^{2πiθ}.
-/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require U to be connected,
-- excluding extensions on an unrelated disjoint component.
theorem lacunarySeries_natural_boundary :
    ¬∃ (U : Set ℂ) (F : ℂ → ℂ),
      IsOpen U ∧ IsConnected U ∧ ball (0 : ℂ) 1 ⊂ U ∧
      DifferentiableOn ℂ F U ∧
      ∀ z ∈ ball (0 : ℂ) 1, F z = lacunarySeries z := by
  rintro ⟨U, F, hU_open, hU_connected, hU_strict, hF, hF_eq⟩
  obtain ⟨z, hzU, hz_norm⟩ :=
    connected_superset_meets_unit_sphere hU_connected hU_strict
  obtain ⟨θ, hθU⟩ :=
    open_mem_unit_sphere_contains_rational_angle hU_open hzU hz_norm
  -- Precise remaining analytic frontier: at the root of unity
  -- `ζ = circleMap 0 1 (2πθ)`, prove that the radial difference quotients
  --
  --   (lacunarySeries ζ - lacunarySeries (r • ζ)) / (1 - r)
  --
  -- are unbounded as `r → 1⁻`.  For all sufficiently large `n`,
  -- `ζ ^ n.factorial = 1`, and each corresponding summand is
  -- `(1 - r ^ n.factorial) / (n.factorial * (1 - r))`, which tends to one.
  -- On the other hand `hF`, `hF_eq`, and `hθU` make the same quotients tend
  -- to the finite derivative of `F` at `ζ`.
  sorry

end
