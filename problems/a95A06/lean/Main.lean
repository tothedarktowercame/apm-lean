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
import Mathlib.Analysis.Calculus.SmoothSeries
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

/-- Differentiating cancels the factorial denominator in each lacunary
summand.  This is the termwise identity used in the boundary-divergence
argument. -/
lemma lacunaryTerm_hasDerivAt (n : ℕ) (z : ℂ) :
    HasDerivAt (lacunaryTerm n) (z ^ (n.factorial - 1)) z := by
  change HasDerivAt (fun w : ℂ => w ^ n.factorial / (n.factorial : ℂ)) _ z
  convert (hasDerivAt_pow n.factorial z).div_const (n.factorial : ℂ) using 1
  field_simp [Nat.factorial_ne_zero]

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

/-- A holomorphic extension across a boundary point has locally bounded
derivative there.  This is the finite side of the Hadamard-gap contradiction;
the other side is the radial divergence of the lacunary derivative series. -/
lemma extension_deriv_eventually_bounded
    {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) :
    ∀ᶠ w in 𝓝 z, ‖deriv F w‖ < ‖deriv F z‖ + 1 := by
  have hderiv_cont : ContinuousAt (deriv F) z := by
    have hderiv_cont_on : ContinuousOn (deriv F) U :=
      (hF.contDiffOn hU : ContDiffOn ℂ 1 F U).continuousOn_deriv_of_isOpen
        hU (by norm_num)
    exact hderiv_cont_on.continuousAt (hU.mem_nhds hz)
  have hnorm_cont : ContinuousAt (fun w => ‖deriv F w‖) z :=
    continuous_norm.continuousAt.comp hderiv_cont
  exact (hnorm_cont.tendsto.eventually (gt_mem_nhds (by linarith))).mono
    (fun _ hw => hw)

/-- Inside the unit disk, the derivative of the lacunary series is the
termwise derivative series.  The derivative series is controlled on a
slightly larger disk by a geometric majorant. -/
lemma lacunarySeries_hasDerivAt_of_norm_lt_one
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt lacunarySeries (∑' n : ℕ, z ^ (n.factorial - 1)) z := by
  let ρ : ℝ := (‖z‖ + 1) / 2
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    linarith
  have hzρ : ‖z‖ < ρ := by
    dsimp [ρ]
    linarith
  let u : ℕ → ℝ := fun n => ρ⁻¹ * ρ ^ n
  have hu : Summable u := by
    exact (summable_geometric_of_lt_one hρ0.le hρ1).mul_left ρ⁻¹
  have hbound : ∀ n (y : ℂ), y ∈ ball (0 : ℂ) ρ →
      ‖y ^ (n.factorial - 1)‖ ≤ u n := by
    intro n y hy
    rw [mem_ball, dist_zero_right] at hy
    by_cases hn : n = 0
    · subst n
      simpa [u] using (one_le_inv₀ hρ0).2 hρ1.le
    · have hpow_base : ‖y‖ ^ (n.factorial - 1) ≤ ρ ^ (n.factorial - 1) :=
        pow_le_pow_left₀ (norm_nonneg y) hy.le _
      have hexp : n - 1 ≤ n.factorial - 1 :=
        Nat.sub_le_sub_right n.self_le_factorial 1
      have hpow_exp : ρ ^ (n.factorial - 1) ≤ ρ ^ (n - 1) :=
        pow_le_pow_of_le_one hρ0.le hρ1.le hexp
      calc
        ‖y ^ (n.factorial - 1)‖ = ‖y‖ ^ (n.factorial - 1) := norm_pow _ _
        _ ≤ ρ ^ (n.factorial - 1) := hpow_base
        _ ≤ ρ ^ (n - 1) := hpow_exp
        _ = u n := by
          change ρ ^ (n - 1) = ρ⁻¹ * ρ ^ n
          have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          rw [mul_comm, ← div_eq_mul_inv, eq_div_iff hρ0.ne']
          rw [← pow_succ, Nat.sub_add_cancel hn1]
  change HasDerivAt (fun w => ∑' n, lacunaryTerm n w)
    (∑' n : ℕ, z ^ (n.factorial - 1)) z
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball 0 ρ).isPreconnected
    (fun n y _ => lacunaryTerm_hasDerivAt n y) hbound
    (mem_ball_self hρ0) (summable_lacunaryTerm_of_mem_closedBall (by simp))
    (by simpa [mem_ball, dist_zero_right] using hzρ)

/-- An extension agreeing with the lacunary series on the unit disk has the
same derivative there, hence the same termwise derivative series. -/
lemma extension_deriv_eq_lacunary_deriv_series
    {F : ℂ → ℂ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1)
    (hF_eq : ∀ z ∈ ball (0 : ℂ) 1, F z = lacunarySeries z) :
    deriv F w = ∑' n : ℕ, w ^ (n.factorial - 1) := by
  have heq : F =ᶠ[𝓝 w] lacunarySeries :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hw)
      (fun v hv => hF_eq v hv)
  rw [heq.deriv_eq]
  exact (lacunarySeries_hasDerivAt_of_norm_lt_one
    (by simpa [mem_ball, dist_zero_right] using hw)).deriv

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
  have hfinite_side :
      ∀ᶠ w in 𝓝 (circleMap 0 1 (2 * Real.pi * (θ : ℝ))),
        ‖deriv F w‖ <
          ‖deriv F (circleMap 0 1 (2 * Real.pi * (θ : ℝ)))‖ + 1 :=
    extension_deriv_eventually_bounded hU_open hF hθU
  have hradial_tendsto :
      Tendsto
        (fun r : ℝ => (r : ℂ) * circleMap 0 1 (2 * Real.pi * (θ : ℝ)))
        (𝓝[<] (1 : ℝ))
        (𝓝 (circleMap 0 1 (2 * Real.pi * (θ : ℝ)))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa using (continuous_ofReal.mul continuous_const).tendsto (1 : ℝ)
  have hfinite_radial :
      ∀ᶠ (r : ℝ) in 𝓝[<] (1 : ℝ),
        ‖deriv F
            ((r : ℂ) * circleMap 0 1 (2 * Real.pi * (θ : ℝ)))‖ <
          ‖deriv F (circleMap 0 1 (2 * Real.pi * (θ : ℝ)))‖ + 1 :=
    hradial_tendsto.eventually hfinite_side
  have hderiv_radial (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
      deriv F ((r : ℂ) * circleMap 0 1 (2 * Real.pi * (θ : ℝ))) =
        ∑' n : ℕ,
          ((r : ℂ) * circleMap 0 1 (2 * Real.pi * (θ : ℝ))) ^
            (n.factorial - 1) := by
    let w : ℂ := (r : ℂ) * circleMap 0 1 (2 * Real.pi * (θ : ℝ))
    have hw_norm : ‖w‖ = r := by
      simp [w, abs_of_pos hr0, norm_circleMap_zero]
    have hw_ball : w ∈ ball (0 : ℂ) 1 := by
      simpa [mem_ball, dist_zero_right, hw_norm] using hr1
    rw [show (r : ℂ) * circleMap 0 1 (2 * Real.pi * (θ : ℝ)) = w by rfl]
    exact extension_deriv_eq_lacunary_deriv_series hw_ball hF_eq
  -- Precise remaining analytic frontier: on each fixed smaller disk, apply
  -- `hasDerivAt_tsum_of_isPreconnected` with `lacunaryTerm_hasDerivAt` to get
  --
  --   deriv lacunarySeries (r * ζ) = ∑' n, (r * ζ) ^ (n.factorial - 1).
  --
  -- For `n ≥ θ.den`, `rational_angle_factorial_pow_eq_one` makes the angular
  -- factor constant, while the positive radial tail is unbounded as `r → 1⁻`.
  -- Via `hF_eq`, the left side is `deriv F (r * ζ)`, contradicting the
  -- already-proved eventual bound `hfinite_radial`.  What remains is thus the
  -- radius-dependent summable majorant and the finite-tail lower-bound limit;
  -- the extension/topology side and the termwise derivative identity are done.
  sorry

end
