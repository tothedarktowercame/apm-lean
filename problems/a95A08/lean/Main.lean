import Mathlib
import ConstructionTargets.SchwarzEquality
import ConstructionTargets.UnivalentDeriv

/-!
# APM a95A08 — length of a univalent image of the unit circle

## Statement repairs

None.

## Encoding questions

None. The disk, its image domain, the parametrized boundary curve, and its
arc length are defined directly. Analyticity on a neighborhood of the closed
disk is represented by differentiability on a strictly larger closed disk.
-/

open Complex Metric Set Real MeasureTheory
open scoped Interval Topology

noncomputable section

def apm_a95A08_Delta : Set ℂ := ball 0 1

def apm_a95A08_imageDomain (f : ℂ → ℂ) : Set ℂ :=
  f '' apm_a95A08_Delta

def apm_a95A08_boundaryCurve (f : ℂ → ℂ) (θ : ℝ) : ℂ :=
  f (Complex.exp (Complex.I * (θ : ℂ)))

def apm_a95A08_curveLength (f : ℂ → ℂ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    ‖deriv f (Complex.exp (Complex.I * (θ : ℂ)))‖

/-- The first conjunct, recovered from the earlier a95A08 development at
commit `7ecc95e`. The mean-value property for `f'`, followed by the triangle
inequality for the integral, is enough; Jensen's inequality is unnecessary. -/
lemma apm_a95A08_curveLength_ge_two_pi
    {f : ℂ → ℂ}
    (hf_holo : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (_hf_inj : Set.InjOn f (closedBall 0 1))
    (_hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ = 1) :
    2 * Real.pi ≤ apm_a95A08_curveLength f := by
  rcases hf_holo with ⟨ε, hε, hf⟩
  have hlarge : 1 < 1 + ε := by linarith
  have hf_open : DifferentiableOn ℂ f (ball 0 (1 + ε)) :=
    hf.mono ball_subset_closedBall
  have hderiv_open : DifferentiableOn ℂ (deriv f) (ball 0 (1 + ε)) :=
    hf_open.deriv isOpen_ball
  have hderiv_closed : DifferentiableOn ℂ (deriv f) (closedBall 0 1) :=
    hderiv_open.mono (closedBall_subset_ball hlarge)
  have hderiv_cl : DiffContOnCl ℂ (deriv f) (ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 one_ne_zero]
    exact hderiv_closed
  have hderiv_cl' :
      DiffContOnCl ℂ (deriv f) (ball 0 |(1 : ℝ)|) := by
    simpa only [abs_one] using hderiv_cl
  have hmean : circleAverage (deriv f) 0 1 = deriv f 0 :=
    hderiv_cl'.circleAverage
  have hlength : 0 < 2 * Real.pi := by positivity
  have hintegral :
      ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv f (circleMap 0 1 θ)‖ ≤
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖deriv f (circleMap 0 1 θ)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hlength.le
  have hcurve :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖deriv f (circleMap 0 1 θ)‖) = apm_a95A08_curveLength f := by
    simp only [apm_a95A08_curveLength, circleMap, zero_add]
    congr 1
    funext θ
    norm_num
    rw [mul_comm]
  have havg :
      2 * Real.pi * ‖circleAverage (deriv f) 0 1‖ ≤
        apm_a95A08_curveLength f := by
    calc
      2 * Real.pi * ‖circleAverage (deriv f) 0 1‖ =
          ‖∫ θ in (0 : ℝ)..(2 * Real.pi), deriv f (circleMap 0 1 θ)‖ := by
            rw [circleAverage_def, norm_smul]
            simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hlength]
            field_simp
      _ ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖deriv f (circleMap 0 1 θ)‖ :=
        hintegral
      _ = apm_a95A08_curveLength f := hcurve
  rw [hmean, hf_deriv, mul_one] at havg
  exact havg

/-- If the unit disk is contained in its image, the analytic injection is a
rotation. Reused from the closed historical a95A08 proof at `7ecc95e`. -/
lemma apm_a95A08_rotation_of_disk_subset_image
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_inj : InjOn f (ball 0 1))
    (hf_zero : f 0 = 0) (hf_deriv : ‖deriv f 0‖ = 1)
    (h_subset : ball (0 : ℂ) 1 ⊆ f '' ball 0 1) :
    ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1,
      f z = exp (I * (α : ℂ)) * z := by
  let U : Set ℂ := ball 0 1
  let g : ℂ → ℂ := Function.invFunOn f U
  have hsurj : SurjOn f U U := fun z hz ↦ h_subset hz
  have hg_maps : MapsTo g U U := hsurj.mapsTo_invFunOn
  have hleft : LeftInvOn g f U := hf_inj.leftInvOn_invFunOn
  have hright : RightInvOn g f U := hsurj.rightInvOn_invFunOn
  have hzero_mem : (0 : ℂ) ∈ U := by simp [U]
  have hg_zero : g 0 = 0 := by simpa [hf_zero] using hleft hzero_mem
  have hg_holo : DifferentiableOn ℂ g U := by
    intro w hw
    have hgw : g w ∈ U := hg_maps hw
    have hfgw : f (g w) = w := hright hw
    have hf_at : AnalyticAt ℂ f (g w) :=
      hf_holo.analyticAt (isOpen_ball.mem_nhds hgw)
    have hf_deriv_ne : deriv f (g w) ≠ 0 :=
      ConstructionTargets.UnivalentDeriv.deriv_ne_zero_of_injOn
        isOpen_ball hf_holo hf_inj hgw
    have hgf_at : AnalyticAt ℂ (g ∘ f) (g w) := by
      apply analyticAt_id.congr
      filter_upwards [isOpen_ball.eventually_mem hgw] with z hz
      exact (hleft hz).symm
    rw [← hfgw]
    exact ((analyticAt_comp_iff_of_deriv_ne_zero hf_at hf_deriv_ne).mp hgf_at).differentiableAt
      |>.differentiableWithinAt
  have hg_deriv : ‖deriv g 0‖ = 1 := by
    have hf_at_zero : DifferentiableAt ℂ f (g 0) := by
      rw [hg_zero]
      exact hf_holo.differentiableAt (isOpen_ball.mem_nhds hzero_mem)
    have hg_at_zero : DifferentiableAt ℂ g 0 :=
      hg_holo.differentiableAt (isOpen_ball.mem_nhds hzero_mem)
    have hcomp : deriv (f ∘ g) 0 = deriv f (g 0) * deriv g 0 :=
      deriv_comp 0 hf_at_zero hg_at_zero
    have hcomp_id : deriv (f ∘ g) 0 = 1 := by
      have heq : (f ∘ g) =ᶠ[nhds 0] id := by
        filter_upwards [isOpen_ball.eventually_mem hzero_mem] with z hz
        exact hright hz
      simpa using heq.deriv_eq
    rw [hg_zero] at hcomp
    have hnorm := congrArg norm (hcomp.symm.trans hcomp_id)
    rw [norm_mul, hf_deriv] at hnorm
    simpa using hnorm
  obtain ⟨c, hc, hgc⟩ :=
    ConstructionTargets.SchwarzEquality.exists_unit_mul
      hg_holo hg_maps hg_zero hg_deriv
  let d : ℂ := c⁻¹
  have hc0 : c ≠ 0 := by
    intro hc0
    simp [hc0] at hc
  have hd : ‖d‖ = 1 := by simp [d, hc]
  refine ⟨d.arg, fun z hz ↦ ?_⟩
  have hdz : d * z ∈ U := by
    change d * z ∈ ball (0 : ℂ) 1
    rw [mem_ball, dist_zero_right, norm_mul, hd, one_mul]
    simpa [mem_ball, dist_zero_right] using hz
  have hgdz : g (d * z) = z := by
    rw [hgc (d * z) hdz]
    dsimp [d]
    field_simp
  have hfdz : f z = d * z := by
    calc
      f z = f (g (d * z)) := congrArg f hgdz.symm
      _ = d * z := hright hdz
  rw [hfdz]
  congr 1
  rw [mul_comm]
  simpa [hd] using (Complex.norm_mul_exp_arg_mul_I d).symm

/-- Strict excess of the boundary length rules out containment of the disk.
This is the identity-theorem continuation step from historical commit
`7ecc95e`. -/
lemma apm_a95A08_disk_not_subset_image_of_length_gt
    {f : ℂ → ℂ}
    (hf_holo : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_inj : InjOn f (closedBall 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ = 1)
    (hlen : 2 * Real.pi < apm_a95A08_curveLength f) :
    ¬(ball (0 : ℂ) 1 ⊆ f '' ball 0 1) := by
  intro hsubset
  rcases hf_holo with ⟨ε, hε, hf⟩
  have hlarge : 1 < 1 + ε := by linarith
  have hf_open : DifferentiableOn ℂ f (ball 0 (1 + ε)) :=
    hf.mono ball_subset_closedBall
  obtain ⟨α, hrotation⟩ := apm_a95A08_rotation_of_disk_subset_image
    (hf_open.mono (ball_subset_ball hlarge.le))
    (hf_inj.mono ball_subset_closedBall) hf_zero hf_deriv hsubset
  let c : ℂ := exp (I * (α : ℂ))
  let r : ℂ → ℂ := fun z => c * z
  have hr_analytic : AnalyticOnNhd ℂ r (ball 0 (1 + ε)) := by
    exact analyticOnNhd_const.mul analyticOnNhd_id
  have hevent : f =ᶠ[nhds (0 : ℂ)] r := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    exact hrotation z hz
  have heq : EqOn f r (ball 0 (1 + ε)) :=
    (hf_open.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
      hr_analytic (convex_ball 0 (1 + ε)).isPreconnected
      (mem_ball_self (by linarith)) hevent
  have hc : ‖c‖ = 1 := by simp [c]
  have hderiv (θ : ℝ) : ‖deriv f (exp (I * (θ : ℂ)))‖ = 1 := by
    let z : ℂ := exp (I * (θ : ℂ))
    have hz_norm : ‖z‖ = 1 := by simp [z]
    have hz : z ∈ ball (0 : ℂ) (1 + ε) := by
      rw [mem_ball, dist_zero_right, hz_norm]
      exact hlarge
    have hlocal : f =ᶠ[nhds z] r := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact heq hw
    rw [hlocal.deriv_eq]
    have hr_deriv : deriv r z = c := (hasDerivAt_const_mul c).deriv
    rw [hr_deriv, hc]
  have hlength : apm_a95A08_curveLength f = 2 * Real.pi := by
    simp [apm_a95A08_curveLength, hderiv]
  linarith

theorem apm_a95a08 (f : ℂ → ℂ)
    (hf_holo : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_inj : Set.InjOn f (closedBall 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ = 1) :
    2 * Real.pi ≤ apm_a95A08_curveLength f ∧
    (2 * Real.pi < apm_a95A08_curveLength f →
      ¬(apm_a95A08_Delta ⊆ apm_a95A08_imageDomain f)) := by
  refine ⟨apm_a95A08_curveLength_ge_two_pi hf_holo hf_inj hf_zero hf_deriv, ?_⟩
  exact apm_a95A08_disk_not_subset_image_of_length_gt
    hf_holo hf_inj hf_zero hf_deriv
