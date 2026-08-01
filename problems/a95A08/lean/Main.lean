/-
! # APM a95A08: Length of image curve ≥ 2π, with equality iff Δ ⊆ D

f is analytic near Δ̄, injective on Δ̄, f(0) = 0, |f'(0)| = 1.
(a) The length ℓ(C) of C = f(∂Δ) satisfies ℓ(C) ≥ 2π.
(b) ℓ(C) > 2π only if Δ ⊄ D = f(Δ).

## Proof strategy (from informal proof)

1. **Jensen's inequality**: (1/2π)∫|f'(e^{iθ})| dθ ≥ exp((1/2π)∫log|f'|)
2. **Mean value for harmonic functions**: (1/2π)∫log|f'(e^{iθ})| = log|f'(0)| = 0
3. Combining: ℓ(C) ≥ 2π · exp(0) = 2π.
4. Equality: |f'| ≡ 1 → f is a rotation → Δ ⊆ D.
5. Contrapositive: Δ ⊆ D → Schwarz lemma forces f = rotation → ℓ = 2π.

## Theory boundaries

- Jensen's inequality for integrals with convex functions is available via
  `ConvexOn.le_integral` in Mathlib, but requires measure-theoretic setup.
- The mean value property for log|f'| (subharmonic/harmonic) requires either
  the Poisson integral formula or the fact that log|g| is harmonic when g is
  holomorphic and nonvanishing. Mathlib has harmonic function results but
  the specific mean value formula for log|f'| on the circle is not directly
  available.
- The Schwarz equality case (|f'(0)| = 1 + maps Δ to Δ ⟹ rotation) is not
  in Mathlib's Schwarz.lean — only the inequality `norm_le_norm_of_mapsTo_ball`
  is proved.

## Statement repair

The generated `curveLength` uses interval integral from 0 to 2π of ‖deriv f (exp(I*θ))‖.
This is correct for the arc length formula. We keep it as-is.
The `hf_holo` hypothesis uses `∃ ε > 0, DifferentiableOn ... (closedBall 0 (1+ε))`
which correctly captures "analytic in a neighborhood of Δ̄."
-/

import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ConstructionTargets.SchwarzEquality
import ConstructionTargets.UnivalentDeriv

open Complex Metric Set Real MeasureTheory

noncomputable section

/-- The length of the image curve: ℓ(C) = ∫₀²π ‖f'(e^{iθ})‖ dθ. -/
def curveLength (f : ℂ → ℂ) : ℝ :=
  ∫ θ in (0:ℝ)..(2 * π), ‖deriv f (exp (I * ↑θ))‖

/-- Part 1: ℓ(C) ≥ 2π.

**Blocker:** The proof requires:
1. Jensen's inequality for the convex function exp, applied to log|f'|.
2. The mean value property for the harmonic function log|f'| on the disk.
3. Combining these with |f'(0)| = 1.

Jensen's inequality for integrals (`ConvexOn.le_integral`) is in Mathlib but
requires setting up the probability measure on [0,2π]. The mean value property
for log|f'| requires that log|f'| is harmonic, which holds when f' ≠ 0
(f is univalent ⟹ f' ≠ 0). Mathlib has the Poisson integral formula but not
the specific mean-value-on-circle result for log|holomorphic function|. -/
theorem curve_length_ge_two_pi
    {f : ℂ → ℂ}
    (hf_holo : ∃ ε > 0, DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_inj : InjOn f (closedBall 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ = 1) :
    2 * π ≤ curveLength f := by
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
  have hmean :
      circleAverage (deriv f) 0 1 = deriv f 0 :=
    hderiv_cl'.circleAverage
  have hlength : 0 < 2 * π := by positivity
  have hintegral :
      ‖∫ θ in (0 : ℝ)..(2 * π), deriv f (circleMap 0 1 θ)‖ ≤
        ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 1 θ)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hlength.le
  have hcurve :
      (∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 1 θ)‖) =
        curveLength f := by
    simp only [curveLength, circleMap, zero_add]
    congr 1
    funext θ
    norm_num
    rw [mul_comm]
  have havg :
      2 * π * ‖circleAverage (deriv f) 0 1‖ ≤ curveLength f := by
    calc
      2 * π * ‖circleAverage (deriv f) 0 1‖ =
          ‖∫ θ in (0 : ℝ)..(2 * π), deriv f (circleMap 0 1 θ)‖ := by
            rw [circleAverage_def, norm_smul]
            simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hlength]
            field_simp
      _ ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 1 θ)‖ :=
        hintegral
      _ = curveLength f := hcurve
  rw [hmean, hf_deriv, mul_one] at havg
  exact havg

/-- Part 2: ℓ(C) > 2π ⟹ Δ ⊄ f(Δ).

By contrapositive: if Δ ⊆ f(Δ), then f⁻¹ restricted to Δ is a disk self-map
fixing 0 with |(f⁻¹)'(0)| = 1/|f'(0)| = 1. By Schwarz lemma equality case,
f⁻¹ is a rotation, so f is a rotation, giving |f'| ≡ 1 and ℓ(C) = 2π.

**Blocker:** `ConstructionTargets.SchwarzEquality` supplies the Schwarz equality
case.  What is still missing here is the analytic inverse on the whole disk:
injectivity must first be used to construct a differentiable inverse of `f` on
the contained disk, with derivative norm one at zero. -/
theorem disk_not_subset_image_of_length_gt
    {f : ℂ → ℂ}
    (hf_holo : ∃ ε > 0, DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_inj : InjOn f (closedBall 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ = 1)
    (hlen : 2 * π < curveLength f) :
    ¬(ball (0 : ℂ) 1 ⊆ f '' ball 0 1) := by
  sorry

/-!
## Counterexample to the proposed rotation lemma

The hypotheses below the next declaration do not say that `f` maps the disk
into itself, nor that it is injective.  Reverse containment of the image is not
enough for Schwarz's lemma: `z - 3 * z ^ 2` covers the unit disk but is not a
rotation.  The following declarations machine-check that obstruction while
leaving the original target unchanged for owner review.
-/

private def rotationCounterexample (z : ℂ) : ℂ := z - 3 * z ^ 2

private lemma rotationCounterexample_surj_ball :
    ball (0 : ℂ) 1 ⊆ rotationCounterexample '' ball 0 1 := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa [mem_ball, dist_zero_right] using hw
  obtain ⟨r, hr⟩ : ∃ r : ℂ, (3 : ℂ) * r ^ 2 + (-1 : ℂ) * r + w = 0 := by
    let p : Polynomial ℂ :=
      Polynomial.C 3 * Polynomial.X ^ 2 - Polynomial.X + Polynomial.C w
    have hp : p.degree ≠ 0 := by
      have hdeg : p.natDegree = 2 := by
        dsimp [p]
        compute_degree!
      exact Polynomial.degree_ne_of_natDegree_ne (by rw [hdeg]; norm_num)
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hp
    exact ⟨r, by simpa [p, Polynomial.IsRoot] using hr⟩
  by_cases hrball : ‖r‖ < 1
  · refine ⟨r, ?_, ?_⟩
    · simpa [mem_ball, dist_zero_right]
    · dsimp [rotationCounterexample]
      linear_combination -hr
  · let s : ℂ := (1 / 3 : ℂ) - r
    have hrnorm : 1 ≤ ‖r‖ := le_of_not_gt hrball
    have hrs : (3 : ℂ) * r * s = w := by
      dsimp [s]
      linear_combination -hr
    have hsroot : rotationCounterexample s = w := by
      dsimp [rotationCounterexample, s]
      linear_combination -hr
    have hrsnorm := congrArg norm hrs
    have hs_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
    have hsball : ‖s‖ < 1 := by
      rw [norm_mul, norm_mul] at hrsnorm
      norm_num at hrsnorm
      nlinarith
    refine ⟨s, ?_, hsroot⟩
    simpa [mem_ball, dist_zero_right]

private lemma rotationCounterexample_differentiable :
    Differentiable ℂ rotationCounterexample := by
  intro z
  unfold rotationCounterexample
  fun_prop

private lemma rotationCounterexample_deriv_zero :
    deriv rotationCounterexample 0 = 1 := by
  have h := (hasDerivAt_id (x := (0 : ℂ))).sub
    ((hasDerivAt_const (x := (0 : ℂ)) (c := (3 : ℂ))).mul
      (hasDerivAt_pow 2 0))
  simpa [rotationCounterexample] using h.deriv

private lemma rotationCounterexample_not_rotation :
    ¬ ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1,
      rotationCounterexample z = exp (I * ↑α) * z := by
  rintro ⟨α, hα⟩
  have hhalf : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right]
    norm_num
  have h := congrArg norm (hα (1 / 2) hhalf)
  rw [norm_mul, Complex.norm_exp] at h
  norm_num [rotationCounterexample] at h

/-- A checked counterexample to `rotation_of_disk_subset_image`. -/
theorem rotation_of_disk_subset_image_counterexample :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f (ball 0 1) ∧
      f 0 = 0 ∧
      ‖deriv f 0‖ = 1 ∧
      ball (0 : ℂ) 1 ⊆ f '' ball 0 1 ∧
      ¬ ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1, f z = exp (I * ↑α) * z := by
  refine ⟨rotationCounterexample,
    rotationCounterexample_differentiable.differentiableOn, ?_, ?_,
    rotationCounterexample_surj_ball, rotationCounterexample_not_rotation⟩
  · norm_num [rotationCounterexample]
  · rw [rotationCounterexample_deriv_zero]
    norm_num

/-- If Δ ⊆ D and f(0) = 0, |f'(0)| = 1, then f is a rotation (Schwarz equality).

The injectivity hypothesis is essential: without it, image containment is the
opposite direction from the `MapsTo` hypothesis of Schwarz's lemma.  See
`rotation_of_disk_subset_image_counterexample` above. -/
lemma rotation_of_disk_subset_image
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_inj : InjOn f (ball 0 1))
    (hf_zero : f 0 = 0) (hf_deriv : ‖deriv f 0‖ = 1)
    (h_subset : ball (0 : ℂ) 1 ⊆ f '' ball 0 1) :
    ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1, f z = exp (I * ↑α) * z := by
  let U : Set ℂ := ball 0 1
  let g : ℂ → ℂ := Function.invFunOn f U
  have hsurj : SurjOn f U U := by
    intro z hz
    exact h_subset hz
  have hg_maps : MapsTo g U U := hsurj.mapsTo_invFunOn
  have hleft : LeftInvOn g f U := hf_inj.leftInvOn_invFunOn
  have hright : RightInvOn g f U := hsurj.rightInvOn_invFunOn
  have hzero_mem : (0 : ℂ) ∈ U := by
    simp [U]
  have hg_zero : g 0 = 0 := by
    simpa [hf_zero] using hleft hzero_mem
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
    ConstructionTargets.SchwarzEquality.exists_unit_mul hg_holo hg_maps hg_zero hg_deriv
  let d : ℂ := c⁻¹
  have hc0 : c ≠ 0 := by
    intro hc0
    simp [hc0] at hc
  have hd : ‖d‖ = 1 := by
    simp [d, hc]
  refine ⟨d.arg, fun z hz ↦ ?_⟩
  have hdz : d * z ∈ U := by
    change d * z ∈ ball (0 : ℂ) 1
    rw [mem_ball, dist_zero_right]
    rw [norm_mul, hd, one_mul]
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

/-- Jensen's inequality for the exponential on the circle:
(1/2π) ∫ g ≥ exp((1/2π) ∫ log g) when g > 0.

This follows from the convexity of exp applied to the probability measure
(1/2π) dθ on [0, 2π].

**What was tried:**
- `ConvexOn.le_integral` requires a measure and convexity proof.
- The probability measure on [0,2π] with density 1/(2π) needs to be set up.
- Mathlib's convexity results (`Real.convexOn_exp`) exist but the measure-
  theoretic Jensen inequality needs additional setup. -/
-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). FALSE as previously stated: the
-- statement integrates `Real.log (g θ)` without hypothesising that `log ∘ g` is
-- integrable, and Lean's Bochner integral of a NON-integrable function is 0.
-- Counterexample on [0,2π]: g θ = 1 at θ = 0 and e^(-1/θ) otherwise. That g is
-- measurable, positive everywhere, bounded by 1 and integrable, so it satisfies
-- every hypothesis — but log (g θ) = -1/θ a.e., which is not integrable near 0,
-- so the left side collapses to exp 0 = 1 while the right side is strictly below
-- 1 because 0 < g < 1 a.e. Adding the missing integrability hypothesis.
--
-- Same FAMILY as a01A02 (faithfulness-ledger #4): a Lean junk-value convention —
-- there `ENNReal.toReal ⊤ = 0`, here `∫ (non-integrable) = 0` — silently turning
-- an unbounded quantity into a harmless one. Both are translation defects.
lemma jensen_exp_circle
    {g : ℝ → ℝ} (hg_meas : AEStronglyMeasurable g (volume.restrict (Icc 0 (2 * π))))
    (hg_int : IntegrableOn g (Icc 0 (2 * π)) volume)
    (hg_log_int : IntegrableOn (fun θ => Real.log (g θ)) (Icc 0 (2 * π)) volume)
    (hg_pos : ∀ θ ∈ Icc (0:ℝ) (2 * π), 0 < g θ) :
    Real.exp ((1 / (2 * π)) * ∫ θ in (0:ℝ)..(2 * π), Real.log (g θ)) ≤
      (1 / (2 * π)) * ∫ θ in (0:ℝ)..(2 * π), g θ := by
  let s : Set ℝ := Icc 0 (2 * π)
  have hs : MeasurableSet s := measurableSet_Icc
  have hlength : 0 < 2 * π := by positivity
  have hvol : volume s = ENNReal.ofReal (2 * π) := by
    simp [s, Real.volume_Icc]
  have hvol_ne : volume s ≠ 0 := by
    rw [hvol]
    exact ENNReal.ofReal_ne_zero_iff.mpr hlength
  have hvol_top : volume s ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  have hexp_int :
      IntegrableOn (Real.exp ∘ fun θ => Real.log (g θ)) s volume := by
    refine hg_int.congr_fun ?_ hs
    intro θ hθ
    exact (Real.exp_log (hg_pos θ hθ)).symm
  have hjensen :=
    convexOn_exp.map_set_average_le Real.continuous_exp.continuousOn
      isClosed_univ hvol_ne hvol_top
      (Filter.Eventually.of_forall fun _ => mem_univ _)
      hg_log_int hexp_int
  have havg_exp :
      (⨍ θ in s, Real.exp (Real.log (g θ)) ∂volume) =
        ⨍ θ in s, g θ ∂volume := by
    exact setAverage_congr_fun hs
      (Filter.Eventually.of_forall fun θ hθ => Real.exp_log (hg_pos θ hθ))
  rw [havg_exp] at hjensen
  have hlog_interval :
      (∫ θ in (0 : ℝ)..(2 * π), Real.log (g θ)) =
        ∫ θ in s, Real.log (g θ) ∂volume := by
    rw [intervalIntegral.integral_of_le hlength.le,
      ← integral_Icc_eq_integral_Ioc]
  have hg_interval :
      (∫ θ in (0 : ℝ)..(2 * π), g θ) =
        ∫ θ in s, g θ ∂volume := by
    rw [intervalIntegral.integral_of_le hlength.le,
      ← integral_Icc_eq_integral_Ioc]
  rw [hlog_interval, hg_interval]
  simpa only [setAverage_eq, hvol, measureReal_def,
    ENNReal.toReal_ofReal hlength.le, inv_eq_one_div, smul_eq_mul] using hjensen

end
