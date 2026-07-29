import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# APM a00J06: Power series with nonnegative coefficients has a singularity at z=1

**Problem.** Let `f(z) = Σ_{n=0}^∞ a(n) zⁿ` have radius of convergence `1`
and assume `0 ≤ a(n)` for all `n`. Prove that `z = 1` is a singular point:
`f` cannot be analytically continued onto a disk centered at `z = 1` having
positive radius.

This is a classical result in complex analysis, closely related to the
Pringsheim theorem.

**Statement repair note.**

The informal-solution file `apm-a00J06.md` was harvested with the **wrong
content**: it contains the proof for a00J05 (Cauchy transform of a compact
real set), not a00J06 (singularity of power series with nonneg coefficients).
The proposed Lean statements are entirely for the Cauchy transform problem.
This file implements the correct problem from `a00J06.tex`.

**Proof sketch.**

Suppose `f` extends analytically to a disk `B(1, ρ)` with `ρ > 0`. Pick
`x ∈ (1-ρ, 1)`. Then `f` is analytic in `B(0,1) ∪ B(1,ρ)`, and the Taylor
series of `f` centered at `x` has radius of convergence `R > 1 - x`
(since the disk extends past `z = 1`).

The Taylor coefficients at `x` are:
`b(n) = Σ_{k≥n} C(k,n) a(k) x^{k-n}`

Since `a(k) ≥ 0` and `x > 0`, we have `b(n) ≥ 0`. The series `Σ b(n)(1-x+ε)ⁿ`
converges for small `ε > 0` (radius `> 1-x`). By Tonelli's theorem (all terms
nonneg):

`Σ_n b(n)(1-x+ε)ⁿ = Σ_k a(k)(x + 1-x+ε)^k = Σ_k a(k)(1+ε)^k < ∞`

But `Σ a(k)(1+ε)^k < ∞` means the original series converges at `z = 1+ε > 1`,
contradicting the radius of convergence being exactly `1`.
-/

set_option linter.unusedVariables false in
set_option maxHeartbeats 400000 in
noncomputable section

open FormalMultilinearSeries

namespace ApmCanaries.A00J06

variable {a : ℕ → ℝ}

/-- The formal power series `Σ a(n) zⁿ` as a `FormalMultilinearSeries`. -/
noncomputable def p (a : ℕ → ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  ofScalars ℝ a

/-- The power series `Σ a(n) zⁿ` evaluated at `z`. -/
noncomputable def f (a : ℕ → ℝ) (z : ℝ) : ℝ :=
  (p a).sum z

private lemma radius_gt_one_of_summable_aux
    (ha : ∀ n, 0 ≤ a n) {ε : ℝ} (he : 0 < ε)
    (h : Summable fun n => a n * (1 + ε) ^ n) :
    (1 : ENNReal) < (p a).radius := by
  have h1e_pos : 0 ≤ 1 + ε := le_of_lt (by linarith)
  have h_sum : Summable fun n => ‖ofScalars ℝ a n‖ * (1 + ε) ^ n := by
    simpa only [ofScalars_norm, Real.norm_eq_abs, abs_of_nonneg (ha _)] using h
  have hle : ((Real.toNNReal (1 + ε)) : ENNReal) ≤ (p a).radius := by
    apply (p a).le_radius_of_summable
    simpa [p, Real.coe_toNNReal (1 + ε) h1e_pos] using h_sum
  have hlt : (1 : ENNReal) < ENNReal.ofReal (1 + ε) := by
    rw [ENNReal.one_lt_ofReal]
    linarith
  exact hlt.trans_le (by simpa using hle)

/-- The main theorem: if `f(z) = Σ a(n) zⁿ` has radius of convergence `1`
    and `a(n) ≥ 0` for all `n`, then `f` cannot be analytically continued
    to a disk centered at `z = 1` with positive radius.

    Equivalently: if `f` is analytic in a neighborhood of `z = 1`, then the
    radius of convergence at `0` exceeds `1`, contradicting the hypothesis.

    The formalized proof uses a shorter property of `FormalMultilinearSeries.sum`:
    outside the convergence radius its nonsummable `tsum` is zero. Thus `f`
    vanishes immediately to the right of `1`. The isolated-zero principle for
    an analytic function would make it vanish in a full neighborhood of `1`.
    Immediately to the left, however, the series is summable and strictly
    positive because its coefficients are nonnegative and not all zero.
-/
theorem singular_at_one
    (ha : ∀ n, 0 ≤ a n)
    (h_radius : (p a).radius = 1) :
    ¬ ∃ ρ : ℝ, 0 < ρ ∧ AnalyticAt ℝ (f a) 1 := by
  rintro ⟨_ρ, _hρ, han⟩
  have hzero_right : ∀ x : ℝ, 1 < x → f a x = 0 := by
    intro x hx
    rw [f, p, FormalMultilinearSeries.sum,
      tsum_eq_zero_of_not_summable]
    intro hs
    have hs' : Summable fun n => a n * x ^ n := by
      simpa only [ofScalars_apply_eq, smul_eq_mul] using hs
    have hrad := radius_gt_one_of_summable_aux ha (sub_pos.mpr hx) (by
      simpa only [show 1 + (x - 1) = x by ring, mul_comm] using hs')
    rw [h_radius] at hrad
    exact (lt_irrefl (1 : ENNReal)) hrad
  rcases han.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · have ha_nonzero : ¬ ∀ n, a n = 0 := by
      intro ha0
      have hp0 : p a = 0 := by
        rw [p, ofScalars_series_eq_zero]
        exact funext ha0
      rw [hp0, zero_radius] at h_radius
      exact ENNReal.top_ne_one h_radius
    push_neg at ha_nonzero
    obtain ⟨n, hn⟩ := ha_nonzero
    have hnpos : 0 < a n := (ha n).lt_of_ne' hn
    have hpos_nhds : ∀ᶠ x : ℝ in nhds (1 : ℝ), 0 < x :=
      Ioi_mem_nhds zero_lt_one
    have hpos : ∀ᶠ x : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1), 0 < x :=
      hpos_nhds.filter_mono nhdsWithin_le_nhds
    have hzero' : ∀ᶠ x : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1), f a x = 0 :=
      hzero.filter_mono nhdsWithin_le_nhds
    have hev : ∀ᶠ x : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
        0 < x ∧ x < 1 ∧ f a x = 0 := by
      filter_upwards [hpos, self_mem_nhdsWithin, hzero'] with x hxpos hxlt hfx
      exact ⟨hxpos, hxlt, hfx⟩
    obtain ⟨x, hxpos, hxlt, hfx⟩ := hev.exists
    have hxball : x ∈ Metric.eball (0 : ℝ) (p a).radius := by
      rw [mem_eball_zero_iff, h_radius]
      simpa [Real.enorm_of_nonneg hxpos.le, ENNReal.ofReal_lt_one] using hxlt
    have hs : Summable fun k => a k * x ^ k := by
      have hs' := ((p a).summable_norm_apply hxball).of_norm
      simpa only [p, ofScalars_apply_eq, smul_eq_mul] using hs'
    have hfxpos : 0 < f a x := by
      have hterm : 0 < a n * x ^ n := mul_pos hnpos (pow_pos hxpos n)
      have hnonneg : ∀ k, 0 ≤ a k * x ^ k :=
        fun k => mul_nonneg (ha k) (pow_nonneg hxpos.le k)
      simpa only [f, p, FormalMultilinearSeries.sum, ofScalars_apply_eq,
        smul_eq_mul] using hs.tsum_pos hnonneg n hterm
    exact hfxpos.ne' hfx
  · have hne' : ∀ᶠ x : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1), f a x ≠ 0 :=
      hne.filter_mono (nhdsWithin_mono _ (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt hx))
    have hzero' : ∀ᶠ x : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1), f a x = 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hzero_right x hx
    obtain ⟨x, hxne, hxzero⟩ := (hne'.and hzero').exists
    exact hxne hxzero

/-- If `Σ a(n) (1+ε)^n` converges for some `ε > 0`, then the radius of
    convergence exceeds `1`.

    This follows from `FormalMultilinearSeries.le_radius_of_summable`:
    convergence of `Σ ‖p n‖ rⁿ` at `r` implies radius `≥ r`.
    For `ofScalars ℝ a`, `‖p n‖ = ‖a(n)‖ = |a(n)|` (by `NormOneClass`), and
    `|a(n)| = a(n)` since `a(n) ≥ 0`. -/
lemma radius_gt_one_of_summable (ha : ∀ n, 0 ≤ a n) {ε : ℝ} (he : 0 < ε)
    (h : Summable fun n => a n * (1 + ε) ^ n) :
    (1 : ENNReal) < (p a).radius := by
  exact radius_gt_one_of_summable_aux ha he h

end ApmCanaries.A00J06
