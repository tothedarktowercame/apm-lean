import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# APM a92J04: A self-map of the disk tangent to the identity must be the identity

**Problem.** Let Δ = {z ∈ ℂ : |z| < 1}. Suppose Σ_{n=2}^∞ aₙzⁿ converges
absolutely for all z ∈ Δ, and |z + Σ_{n=2}^∞ aₙzⁿ| < 1 for all z ∈ Δ.
Prove that aₙ = 0 for all n ≥ 2.

## Proof strategy

By the Schwarz lemma equality case: f(z) = z + Σ aₙzⁿ maps Δ to Δ with
f(0) = 0 and f'(0) = 1, so ‖f'(0)‖ = 1. By the rigidity case of the
Schwarz lemma (Mathlib's `affine_of_mapsTo_ball_of_norm_dslope_eq_div`),
f must be affine: f(z) = f(0) + dslope f 0 0 • z = deriv f 0 • z = z.
So f = id, hence all coefficients aₙ vanish.

## Statement repair note

The informal proof proposes encoding the problem via a coefficient sequence
and a `tsum`. The key structural repair: Mathlib's Schwarz lemma uses
`MapsTo f (ball c R₁) (closedBall (f c) R₂)` — it maps to a **closed** ball.
Since the problem gives `|f(z)| < 1` (open ball), and open ball ⊆ closed ball,
this is a strengthening, so the Mathlib lemma applies directly.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Set Metric Filter
open scoped Topology ENNReal NNReal

namespace ApmCanaries.A92J04

/-! ## Schwarz lemma equality case for disk self-maps -/

/-- If f : ball 0 1 → ball 0 1 is analytic with f(0) = 0 and deriv f 0 = 1,
    then f(z) = z for all z in the disk.

    This is the equality case of the Schwarz lemma. -/
theorem disk_selfmap_deriv_one_eq_identity
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hf_maps : ∀ z ∈ ball (0 : ℂ) 1, f z ∈ ball (0 : ℂ) 1)
    (hf_zero : f 0 = 0)
    (hf_deriv : deriv f 0 = 1) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = z := by
  -- The open-ball map implies a closed-ball map
  have h_maps_closed : MapsTo f (ball (0 : ℂ) 1) (closedBall (f 0) 1) := by
    intro z hz
    rw [hf_zero, mem_closedBall]
    exact le_of_lt (mem_ball.mp (hf_maps z hz))
  -- Apply the equality case: ‖dslope f 0 0‖ = ‖deriv f 0‖ = ‖1‖ = 1 = 1/1
  have h_dslope : dslope f 0 0 = deriv f 0 := dslope_same f 0
  have h_eq : ‖dslope f 0 0‖ = 1 / 1 := by
    rw [h_dslope, hf_deriv, one_div, inv_one, norm_one]
  have h_00 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_self]; norm_num
  -- Equality case: f z = f 0 + (z - 0) • dslope f 0 0
  have hθ : EqOn f (fun z => f 0 + (z - 0) • dslope f 0 0) (ball (0 : ℂ) 1) :=
    affine_of_mapsTo_ball_of_norm_dslope_eq_div hf_holo h_maps_closed h_00 h_eq
  -- Simplify: f 0 = 0, dslope f 0 0 = deriv f 0 = 1, so f z = z
  intro z hz
  have := hθ hz
  simp only [sub_zero, h_dslope, hf_deriv, smul_eq_mul, mul_one, hf_zero, zero_add] at this
  exact this

/-! ## Main theorem -/

/-- Main theorem: if f(z) = z + Σ_{n≥2} aₙzⁿ maps Δ into Δ,
    then f(z) = z for all z ∈ Δ. -/
theorem disk_selfmap_tangent_identity
    {a : ℕ → ℂ}
    (hconv : ∀ z ∈ ball (0 : ℂ) 1, Summable (fun n => a (n + 2) * z ^ (n + 2)))
    (hf_maps : ∀ z ∈ ball (0 : ℂ) 1,
      ‖z + ∑' n, a (n + 2) * z ^ (n + 2)‖ < 1) :
    ∀ n, 2 ≤ n → a n = 0 := by
  let c : ℕ → ℂ := fun n => a (n + 2)
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ c
  have hp_radius : (1 : ℝ≥0∞) ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hr_lt_one : (r : ℝ) < 1 := by exact_mod_cast hr
    by_cases hr0 : r = 0
    · simp [hr0]
    have hr_pos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr0)
    have hr_ball : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right, norm_real, Real.norm_of_nonneg (NNReal.zero_le_coe)]
      exact hr_lt_one
    have hs := hconv (r : ℂ) hr_ball
    have hs' : Summable (fun n => c n * (r : ℂ) ^ n) := by
      have hmul := hs.mul_left (((r : ℂ) ^ 2)⁻¹)
      apply hmul.congr
      intro n
      simp only [c, pow_add]
      field_simp [NNReal.coe_ne_zero.mpr hr0]
    apply p.le_radius_of_tendsto
    have ht := hs'.tendsto_atTop_zero.norm
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      norm_real, NNReal.norm_eq] using ht
  have hp_pos : 0 < p.radius := (by norm_num : (0 : ℝ≥0∞) < 1).trans_le hp_radius
  have hp_series := p.hasFPowerSeriesOnBall hp_pos
  have hp_diff : DifferentiableOn ℂ p.sum (ball (0 : ℂ) 1) := by
    apply hp_series.differentiableOn.mono
    intro z hz
    rw [mem_eball_zero_iff]
    have hz' : ‖z‖₊ < (1 : ℝ≥0) := by
      simpa [mem_ball, dist_zero_right] using hz
    exact (ENNReal.coe_lt_coe.mpr hz').trans_le hp_radius
  have htail (z : ℂ) :
      z ^ 2 * p.sum z = ∑' n, a (n + 2) * z ^ (n + 2) := by
    change z ^ 2 * FormalMultilinearSeries.ofScalarsSum c z =
      ∑' n, a (n + 2) * z ^ (n + 2)
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [c, smul_eq_mul]
    ring
  let f : ℂ → ℂ := fun z => z + z ^ 2 * p.sum z
  have hf_diff : DifferentiableOn ℂ f (ball (0 : ℂ) 1) := by
    exact differentiableOn_id.add
      ((differentiableOn_id.pow 2).mul hp_diff)
  have hf_ball : ∀ z ∈ ball (0 : ℂ) 1, f z ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    simpa only [f, htail z] using hf_maps z hz
  have hf_zero : f 0 = 0 := by simp [f]
  have hf_deriv : deriv f 0 = 1 := by
    have hg : DifferentiableAt ℂ p.sum 0 :=
      hp_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))
    have hd : HasDerivAt f 1 0 := by
      dsimp only [f]
      convert (hasDerivAt_id 0).add (((hasDerivAt_id 0).pow 2).mul hg.hasDerivAt) using 1
      simp
    exact hd.deriv
  have hf_id := disk_selfmap_deriv_one_eq_identity hf_diff hf_ball hf_zero hf_deriv
  have hp_zero_ne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → p.sum z = 0 := by
    intro z hz hz0
    have h := hf_id z hz
    simp only [f, add_eq_left] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hz0)
  have hp_sum_zero : ∀ z ∈ ball (0 : ℂ) 1, p.sum z = 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      have heq : p.sum =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
        change ∀ᶠ w in 𝓝[≠] (0 : ℂ), p.sum w = 0
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
        intro hw0
        exact hp_zero_ne w hw hw0
      have hlim : Tendsto p.sum (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
        (tendsto_congr' heq).mpr tendsto_const_nhds
      have hcont_ne : Tendsto p.sum (𝓝[≠] (0 : ℂ)) (𝓝 (p.sum 0)) :=
        continuousAt_iff_punctured_nhds.mp
          (hp_diff.differentiableAt
            (Metric.isOpen_ball.mem_nhds (by simp))).continuousAt
      exact tendsto_nhds_unique
        hcont_ne hlim
    · exact hp_zero_ne z hz hz0
  have hball : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) 1 :=
    Metric.ball_mem_nhds (0 : ℂ) zero_lt_one
  have hevent : p.sum =ᶠ[𝓝 (0 : ℂ)] 0 :=
    hball.mono hp_sum_zero
  have hp_eq_zero : p = 0 :=
    hp_series.hasFPowerSeriesAt.eq_zero_of_eventually hevent
  have hc_zero : c = 0 := by
    exact (FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).mp
      (by simpa [p] using hp_eq_zero)
  intro n hn
  have := congrFun hc_zero (n - 2)
  simpa [c, Nat.sub_add_cancel hn] using this

/-- Direct version: if f : ℂ → ℂ is differentiable on the disk, maps disk to disk,
    fixes 0, and has deriv f 0 = 1, then f = id. -/
theorem disk_selfmap_tangent_identity' (f : ℂ → ℂ)
    (hf_holo : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hf_maps : ∀ z ∈ ball (0 : ℂ) 1, f z ∈ ball (0 : ℂ) 1)
    (hf_zero : f 0 = 0)
    (hf_deriv : deriv f 0 = 1) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = z :=
  disk_selfmap_deriv_one_eq_identity hf_holo hf_maps hf_zero hf_deriv

end ApmCanaries.A92J04
