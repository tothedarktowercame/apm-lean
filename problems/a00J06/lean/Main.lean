import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

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

/-!
### Statement repair: honest Pringsheim theorem

The original `singular_at_one` above is a junk-value argument (the `tsum` of a
nonsummable series is zero outside the radius).  Here we prove Pringsheim's
theorem honestly for complex scalars: if `a n ≥ 0` and the power series has
radius of convergence exactly `1`, the function `z ↦ ∑' a n zⁿ` admits no
analytic continuation through `z = 1`.
-/

namespace ApmCanaries.A00J06.Pringsheim

open FormalMultilinearSeries

/-- The function `z ↦ ∑' n, (a n : ℂ) * z ^ n`. -/
private noncomputable def ApmF (a : ℕ → ℝ) (z : ℂ) : ℂ := ∑' n, (a n : ℂ) * z ^ n

/-- The double array `a (n+k) * C(n+k,k) * c^n * t^k`, indexed by the pair `(k, n)`. -/
private def ApmV (a : ℕ → ℝ) (c t : ℝ) : ℕ × ℕ → ℝ := fun p =>
  a (p.2 + p.1) * ((p.2 + p.1).choose p.1 : ℝ) * c ^ p.2 * t ^ p.1

private lemma apmV_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    0 ≤ ApmV a c t :=
  fun p => mul_nonneg (mul_nonneg (mul_nonneg (ha _) (Nat.cast_nonneg _))
    (pow_nonneg hc _)) (pow_nonneg ht _)

/-- Binomial identity along the antidiagonal, real version. -/
private lemma apm_antidiag_sum (a : ℕ → ℝ) (c t : ℝ) (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal m, ApmV a c t p = a m * (c + t) ^ m := by
  have h : ∀ p ∈ Finset.antidiagonal m,
      ApmV a c t p = a m * (m.choose p.1 * (t ^ p.1 * c ^ p.2)) := by
    intro p hp
    have hpm : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
    simp only [ApmV]
    rw [← hpm, Nat.add_comm]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, add_comm c t,
    Commute.add_pow' (Commute.all t c) m]
  simp

/-- Binomial identity along the antidiagonal, complex version. -/
private lemma apm_antidiag_sum_complex (a : ℕ → ℝ) (w y : ℂ) (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal m,
        ((a (p.2 + p.1) : ℂ) * ((p.2 + p.1).choose p.1 : ℝ) * w ^ p.2 * y ^ p.1)
      = (a m : ℂ) * (w + y) ^ m := by
  have h : ∀ p ∈ Finset.antidiagonal m,
      ((a (p.2 + p.1) : ℂ) * ((p.2 + p.1).choose p.1 : ℝ) * w ^ p.2 * y ^ p.1)
        = (a m : ℂ) * (m.choose p.1 * (y ^ p.1 * w ^ p.2)) := by
    intro p hp
    have hpm : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
    rw [← hpm, Nat.add_comm]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, add_comm w y,
    Commute.add_pow' (Commute.all y w) m]
  simp

/-- Tonelli for the nonnegative double array: summability of the whole array,
of each row, and of the row sums, from summability of `∑ a m (c+t)^m`. -/
private lemma apm_summable_V (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hct : c + t < 1) (hs : Summable fun m => a m * (c + t) ^ m) :
    Summable (ApmV a c t) ∧ (∀ k, Summable fun n => ApmV a c t (k, n))
      ∧ Summable fun k => ∑' n, ApmV a c t (k, n) := by
  have hnn : 0 ≤ ApmV a c t := apmV_nonneg a ha hc ht
  have hfib : ∀ m : ℕ, Summable fun p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m} =>
      ApmV a c t p := fun m => (hasSum_fintype _).summable
  have hcol : Summable fun m => ∑' p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m},
      ApmV a c t p := by
    have he : ∀ m, (∑' p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m}, ApmV a c t p)
        = a m * (c + t) ^ m := by
      intro m
      rw [tsum_fintype, ← Finset.sum_subtype (Finset.antidiagonal m) (fun _ => Iff.rfl)]
      exact apm_antidiag_sum a c t m
    exact hs.congr (fun m => (he m).symm)
  have hsig : Summable fun s : Σ m : ℕ, {p : ℕ × ℕ // p ∈ Finset.antidiagonal m} =>
      ApmV a c t s.2 :=
    (summable_sigma_of_nonneg (fun s => hnn _)).mpr ⟨hfib, hcol⟩
  have hprod : Summable (ApmV a c t) := by
    exact Finset.sigmaAntidiagonalEquivProd.summable_iff.mp hsig
  exact ⟨hprod, ((summable_prod_of_nonneg hnn).mp hprod).1,
    ((summable_prod_of_nonneg hnn).mp hprod).2⟩

/-- The value of the iterated sum. -/
private lemma apm_tsum_V (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hct : c + t < 1) (hs : Summable fun m => a m * (c + t) ^ m) :
    ∑' k, ∑' n, ApmV a c t (k, n) = ∑' m, a m * (c + t) ^ m := by
  obtain ⟨hprod, hrows, hcolsum⟩ := apm_summable_V a ha hc ht hct hs
  have hfib : ∀ m : ℕ, Summable fun p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m} =>
      ApmV a c t p := fun m => (hasSum_fintype _).summable
  have he : ∀ m, (∑' p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m}, ApmV a c t p)
      = a m * (c + t) ^ m := by
    intro m
    rw [tsum_fintype, ← Finset.sum_subtype (Finset.antidiagonal m) (fun _ => Iff.rfl)]
    exact apm_antidiag_sum a c t m
  have hcol : Summable fun m => ∑' p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m},
      ApmV a c t p := hs.congr (fun m => (he m).symm)
  have hsig : Summable fun s : Σ m : ℕ, {p : ℕ × ℕ // p ∈ Finset.antidiagonal m} =>
      ApmV a c t s.2 :=
    (summable_sigma_of_nonneg (fun s => apmV_nonneg a ha hc ht _)).mpr ⟨hfib, hcol⟩
  have h1 : ∑' s : Σ m : ℕ, {p : ℕ × ℕ // p ∈ Finset.antidiagonal m}, ApmV a c t s.2
      = ∑' p : ℕ × ℕ, ApmV a c t p :=
    Equiv.tsum_eq Finset.sigmaAntidiagonalEquivProd _
  rw [(hprod.tsum_prod' hrows).symm, ← h1]
  exact (hsig.tsum_sigma' hfib).trans (by rw [funext he])

/-- Complex version of the double array. -/
private def ApmU (a : ℕ → ℝ) (w y : ℂ) : ℕ × ℕ → ℂ := fun p =>
  ((a (p.2 + p.1) : ℂ) * ((p.2 + p.1).choose p.1 : ℝ) * w ^ p.2 * y ^ p.1)

set_option maxHeartbeats 1000000 in
/-- Complex version of the swap. -/
private lemma apm_key_complex (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {w y : ℂ}
    (hy : ‖w‖ + ‖y‖ < 1) (hs : Summable fun m => a m * (‖w‖ + ‖y‖) ^ m) :
    (∀ k, Summable fun n => ApmU a w y (k, n))
      ∧ ∑' k, ∑' n, ApmU a w y (k, n)
        = ∑' m, (a m : ℂ) * (w + y) ^ m := by
  obtain ⟨hprod, hrows, hcolsum⟩ :=
    apm_summable_V a ha (norm_nonneg w) (norm_nonneg y) hy hs
  have hnorm : ∀ p, ‖ApmU a w y p‖ = ApmV a ‖w‖ ‖y‖ p := by
    intro p
    show ‖((a (p.2 + p.1) : ℂ) * ((p.2 + p.1).choose p.1 : ℝ) * w ^ p.2
        * y ^ p.1)‖ = _
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_mul, Complex.norm_pow,
      Complex.norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (ha _), abs_of_nonneg (Nat.cast_nonneg _)]
    rfl
  have hU : Summable (ApmU a w y) := by
    refine Summable.of_norm (f := ApmU a w y) ?_
    exact hprod.congr fun p => (hnorm p).symm
  have hrows' : ∀ k, Summable fun n => ApmU a w y (k, n) := fun k => hU.prod_factor k
  have hfib : ∀ m : ℕ, Summable fun p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m} =>
      ApmU a w y p := fun m => (hasSum_fintype _).summable
  have hUsig : Summable fun s : Σ m : ℕ, {p : ℕ × ℕ // p ∈ Finset.antidiagonal m} =>
      ApmU a w y s.2 := Finset.sigmaAntidiagonalEquivProd.summable_iff.mpr hU
  have he : ∀ m, (∑' p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m}, ApmU a w y p)
      = (a m : ℂ) * (w + y) ^ m := by
    intro m
    rw [tsum_fintype, ← Finset.sum_subtype (Finset.antidiagonal m) (fun _ => Iff.rfl)]
    exact apm_antidiag_sum_complex a w y m
  refine ⟨fun k => hrows' k, ?_⟩
  rw [(hU.tsum_prod' hrows').symm]
  have h1 : ∑' s : Σ m : ℕ, {p : ℕ × ℕ // p ∈ Finset.antidiagonal m}, ApmU a w y s.2
      = ∑' p : ℕ × ℕ, ApmU a w y p := Equiv.tsum_eq Finset.sigmaAntidiagonalEquivProd _
  rw [← h1]
  exact (hUsig.tsum_sigma' hfib).trans (by rw [funext he])

/-- Taylor coefficients at `c` of the power series: `B k = ∑_{n} a (n+k) C(n+k,k) c^n`. -/
private noncomputable def ApmB (a : ℕ → ℝ) (c : ℝ) (k : ℕ) : ℝ :=
  ∑' n, a (n + k) * ((n + k).choose k : ℝ) * c ^ n

/-- For nonnegative summable `f`, each finite initial sum is at most the total. -/
private lemma apm_range_le_tsum {f : ℕ → ℝ} (hf : 0 ≤ f) (hsum : Summable f) (N : ℕ) :
    ∑ n ∈ Finset.range N, f n ≤ ∑' n, f n := by
  have hstep : ∀ n, (∑ i ∈ Finset.range n, f i) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
    intro n
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hf n)
  exact (monotone_nat_of_le_succ hstep).ge_of_tendsto (hsum.hasSum.tendsto_sum_nat) N

/-- For nonnegative summable `f`, each term is at most the total. -/
private lemma apm_single_le_tsum {f : ℕ → ℝ} (hf : 0 ≤ f) (hsum : Summable f) (k : ℕ) :
    f k ≤ ∑' n, f n := by
  have h1 : HasSum (fun n => if n = k then f k else 0) (f k) := hasSum_ite_eq k (f k)
  refine hasSum_le (fun n => ?_) h1 hsum.hasSum
  by_cases h : n = k
  · simp [h]
  · simp only [if_neg h, zero_le]
    exact hf n

private lemma apmB_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (k : ℕ) :
    0 ≤ ApmB a c k :=
  tsum_nonneg fun n => mul_nonneg (mul_nonneg (ha _) (Nat.cast_nonneg _)) (pow_nonneg hc _)

private lemma apmB_summable (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (hc1 : c < 1)
    (hsum : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun m => a m * ρ ^ m) (k : ℕ) :
    Summable fun n => a (n + k) * ((n + k).choose k : ℝ) * c ^ n := by
  have ht0pos : 0 < (1 - c) / 2 := by linarith
  have hct : c + (1 - c) / 2 < 1 := by nlinarith
  have hs0 : Summable fun m => a m * ((1 + c) / 2) ^ m := hsum _ (by linarith) (by linarith)
  have hP : ∀ m : ℕ, (c + (1 - c) / 2) ^ m = ((1 + c) / 2) ^ m := fun m => by
    rw [show c + (1 - c) / 2 = (1 + c) / 2 by ring]
  have hs' : Summable fun m => a m * (c + (1 - c) / 2) ^ m :=
    hs0.congr fun m => by rw [hP m]
  obtain ⟨hV, hrows, hcol⟩ := apm_summable_V a ha hc ht0pos.le hct hs'
  have hnnV : 0 ≤ ApmV a c ((1 - c) / 2) := fun p => mul_nonneg (mul_nonneg
    (mul_nonneg (ha _) (Nat.cast_nonneg _)) (pow_nonneg hc _)) (pow_nonneg ht0pos.le _)
  have htotal : ∑' k', ∑' n, ApmV a c ((1 - c) / 2) (k', n)
      = ∑' m, a m * (c + (1 - c) / 2) ^ m :=
    apm_tsum_V a ha hc ht0pos.le hct hs'
  have hrowle : (∑' n, ApmV a c ((1 - c) / 2) (k, n))
      ≤ ∑' m, a m * (c + (1 - c) / 2) ^ m := by
    rw [← htotal]
    exact apm_single_le_tsum (fun k' => tsum_nonneg fun n => hnnV (k', n)) hcol k
  have hbnd : ∀ N, ∑ n ∈ Finset.range N, a (n + k) * ((n + k).choose k : ℝ) * c ^ n
      ≤ (∑' m, a m * (c + (1 - c) / 2) ^ m) / ((1 - c) / 2) ^ k := by
    intro N
    refine (le_div_iff₀ (pow_pos ht0pos k)).mpr ?_
    rw [Finset.sum_mul]
    have h2 : ∀ n ∈ Finset.range N, a (n + k) * ((n + k).choose k : ℝ) * c ^ n
        * ((1 - c) / 2) ^ k = ApmV a c ((1 - c) / 2) (k, n) := by
      intro n _
      rw [ApmV]
    rw [Finset.sum_congr rfl h2]
    refine le_trans (apm_range_le_tsum (fun n => hnnV (k, n)) (hrows k) N) hrowle
  exact summable_of_sum_range_le (fun n => mul_nonneg (mul_nonneg (ha _)
    (Nat.cast_nonneg _)) (pow_nonneg hc _)) hbnd

private lemma apmB_mul_eq (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hct : c + t < 1) (hsum : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun m => a m * ρ ^ m)
    (k : ℕ) :
    ApmB a c k * t ^ k = ∑' n, ApmV a c t (k, n) := by
  have hc1 : c < 1 := lt_of_le_of_lt (by linarith) hct
  have hs : Summable fun m => a m * (c + t) ^ m := hsum _ (by linarith) hct
  have hrow := apmB_summable a ha hc hc1 hsum
  obtain ⟨hV, hrows, hcol⟩ := apm_summable_V a ha hc ht hct hs
  rw [ApmB, ← tsum_mul_right]
  exact congrArg tsum (funext fun n => rfl)

private lemma apmB_scale_summable (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hct : c + t < 1) (hsum : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun m => a m * ρ ^ m) :
    Summable fun k => ApmB a c k * t ^ k := by
  have hs : Summable fun m => a m * (c + t) ^ m := hsum _ (by linarith) hct
  obtain ⟨hV, hrows, hcol⟩ := apm_summable_V a ha hc ht hct hs
  exact hcol.congr fun k => (apmB_mul_eq a ha hc ht hct hsum k).symm

private lemma apm_tsum_B (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hct : c + t < 1) (hsum : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun m => a m * ρ ^ m) :
    ∑' k, ApmB a c k * t ^ k = ∑' m, a m * (c + t) ^ m := by
  have hs : Summable fun m => a m * (c + t) ^ m := hsum _ (by linarith) hct
  obtain ⟨hV, hrows, hcol⟩ := apm_summable_V a ha hc ht hct hs
  have hscal : Summable fun k => ApmB a c k * t ^ k :=
    hcol.congr fun k => (apmB_mul_eq a ha hc ht hct hsum k).symm
  rw [funext fun k => apmB_mul_eq a ha hc ht hct hsum k]
  exact apm_tsum_V a ha hc ht hct hs

set_option maxHeartbeats 10000000 in
/-- The power series expansion of `ApmF a` at `c ∈ (0,1)` with coefficients `ApmB`. -/
private lemma apm_hasFPS (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hc1 : 0 < c) (hc2 : c < 1)
    (hsum : Summable fun m => a m * ((1 + c) / 2) ^ m) :
    HasFPowerSeriesAt (ApmF a)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => (ApmB a c k : ℂ))) (c : ℂ) := by
  let R : ℝ := (1 - c) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hc0 : 0 ≤ c := hc1.le
  have hmid : c + R = (1 + c) / 2 := by dsimp [R]; ring
  obtain ⟨hV, hrowV, hcolV⟩ := apm_summable_V a ha hc0 hR.le
    (by rw [hmid]; linarith) (by simpa [hmid] using hsum)
  have hrow : ∀ k, Summable fun n =>
      a (n + k) * ((n + k).choose k : ℝ) * c ^ n := by
    intro k
    refine ((hrowV k).mul_left (R ^ k)⁻¹).congr fun n => ?_
    simp only [ApmV]
    field_simp
  have hscal : Summable fun k => ApmB a c k * R ^ k := by
    refine hcolV.congr fun k => ?_
    rw [ApmB, ← tsum_mul_right]
    rfl
  refine ⟨ENNReal.ofReal R, ?_, ENNReal.ofReal_pos.2 hR, ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_summable
      (p := FormalMultilinearSeries.ofScalars ℂ (fun k => (ApmB a c k : ℂ)))
      (r := Real.toNNReal R) ?_
    simpa [FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal _ hR.le,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (apmB_nonneg a ha hc0 _)] using hscal
  · intro y hy
    have hyn : ‖y‖ < R := by
      rw [mem_eball_zero_iff, ← ofReal_norm] at hy
      exact (ENNReal.ofReal_lt_ofReal_iff hR).mp hy
    have hlt : c + ‖y‖ < (1 + c) / 2 := by rw [← hmid]; linarith
    have hs' : Summable fun m => a m * (c + ‖y‖) ^ m :=
      Summable.of_nonneg_of_le
        (fun n => mul_nonneg (ha n) (pow_nonneg (by positivity) n))
        (fun n => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hlt.le n) (ha n)) hsum
    have hy : ‖(c : ℂ)‖ + ‖y‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
      linarith
    have hs'' : Summable fun m => a m * (‖(c : ℂ)‖ + ‖y‖) ^ m := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0] using hs'
    obtain ⟨hrows, hval⟩ := apm_key_complex (w := (c : ℂ)) (y := y) a ha hy hs''
    have heq : ∀ k, (∑' n, ApmU a (c : ℂ) y (k, n)) = (ApmB a c k : ℂ) * y ^ k := by
      intro k
      have hcSum : HasSum (fun n => ((a (n + k) * ((n + k).choose k : ℝ) * c ^ n : ℝ) : ℂ))
          (ApmB a c k : ℂ) := by
        simpa [ApmB] using Complex.ofRealCLM.hasSum (hrow k).hasSum
      rw [← hcSum.tsum_eq, ← tsum_mul_right]
      congr 1
      funext n
      simp [ApmU]
    have hsy : Summable fun k => (ApmB a c k : ℂ) * y ^ k := by
      refine Summable.of_norm_bounded hscal (fun k => ?_)
      simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (apmB_nonneg a ha hc0 k), Complex.norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hyn.le k)
        (apmB_nonneg a ha hc0 k)
    have hvalue : ∑' k, (ApmB a c k : ℂ) * y ^ k = ApmF a ((c : ℂ) + y) := by
      rw [show (fun k => (ApmB a c k : ℂ) * y ^ k) =
        (fun k => ∑' n, ApmU a (c : ℂ) y (k, n)) by funext k; exact (heq k).symm,
        hval]
      rfl
    have hh := hsy.hasSum
    rw [hvalue] at hh
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hh

/-- Taylor coefficients at a complex center. -/
private noncomputable def ApmBz (a : ℕ → ℝ) (w : ℂ) (k : ℕ) : ℂ :=
  ∑' n, (a (n + k) : ℂ) * ((n + k).choose k : ℝ) * w ^ n

private lemma apm_analyticAt (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hsum : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → Summable fun n => a n * ρ ^ n)
    {z : ℂ} (hz : ‖z‖ < 1) : AnalyticAt ℂ (ApmF a) z := by
  have hrowB := apmB_summable a ha (norm_nonneg z) hz hsum
  have hrowz : ∀ k, Summable fun n => (a (n + k) : ℂ) * ((n + k).choose k : ℝ) * z ^ n := by
    intro k
    refine Summable.of_norm (f := fun n => (a (n + k) : ℂ) * ((n + k).choose k : ℝ) * z ^ n) ?_
    refine (hrowB k).congr fun n => ?_
    simp only [Complex.norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (ha (n + k)), abs_of_nonneg
      (Nat.cast_nonneg ((n + k).choose k))]
  have hznorm : ∀ k n, ‖(a (n + k) : ℂ) * ((n + k).choose k : ℝ) * z ^ n‖
      = a (n + k) * ((n + k).choose k : ℝ) * ‖z‖ ^ n := by
    intro k n
    simp only [Complex.norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (ha (n + k)), abs_of_nonneg
      (Nat.cast_nonneg ((n + k).choose k))]
  have hBznorm : ∀ k, ‖ApmBz a z k‖ ≤ ApmB a ‖z‖ k := by
    intro k
    rw [ApmBz]
    refine le_trans (norm_tsum_le_tsum_norm
      (f := fun n => (a (n + k) : ℂ) * ((n + k).choose k : ℝ) * z ^ n)
      ((hrowB k).congr fun n => (hznorm k n).symm)) ?_
    rw [← funext fun n => (hznorm k n).symm, ApmB]
  have hRpos : 0 < (1 - ‖z‖) / 2 := by nlinarith [norm_nonneg z]
  have hR1 : ‖z‖ + (1 - ‖z‖) / 2 < 1 := by nlinarith [norm_nonneg z]
  have hscal := apmB_scale_summable a ha (norm_nonneg z) hRpos.le hR1 hsum
  have hball : HasFPowerSeriesOnBall (ApmF a)
      (FormalMultilinearSeries.ofScalars ℂ (ApmBz a z)) z (ENNReal.ofReal ((1 - ‖z‖) / 2)) := by
    refine ⟨?_, ENNReal.ofReal_pos.2 hRpos, ?_⟩
    · refine FormalMultilinearSeries.le_radius_of_summable
        (p := FormalMultilinearSeries.ofScalars ℂ (ApmBz a z))
        (r := Real.toNNReal ((1 - ‖z‖) / 2)) ?_
      refine Summable.of_norm_bounded hscal (fun k => ?_)
      rw [FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal _ hRpos.le,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
          (pow_nonneg hRpos.le _))]
      exact mul_le_mul_of_nonneg_right (hBznorm k) (pow_nonneg hRpos.le _)
    · intro y hy
      have hyn : ‖y‖ < (1 - ‖z‖) / 2 := by
        rw [mem_eball_zero_iff, ← ofReal_norm] at hy
        exact (ENNReal.ofReal_lt_ofReal_iff hRpos).mp hy
      have hy' : ‖z‖ + ‖y‖ < 1 := by linarith
      obtain ⟨hrowsU, hvalU⟩ := apm_key_complex a ha hy' (hsum _ (add_nonneg (norm_nonneg z) (norm_nonneg y)) hy')
      have hroweq : ∀ k, (∑' n, ApmU a z y (k, n)) = ApmBz a z k * y ^ k := by
        intro k
        have h3 : ∀ n, ApmU a z y (k, n)
            = ((a (n + k) : ℂ) * ((n + k).choose k : ℝ) * z ^ n) * y ^ k :=
          fun n => rfl
        rw [funext h3, ApmBz, tsum_mul_right]
      have hsyz : Summable fun k => ApmBz a z k * y ^ k := by
        refine Summable.of_norm_bounded hscal (fun k => ?_)
        rw [Complex.norm_mul, Complex.norm_pow]
        calc ‖ApmBz a z k‖ * ‖y‖ ^ k ≤ ApmB a ‖z‖ k * ‖y‖ ^ k :=
              mul_le_mul_of_nonneg_right (hBznorm k) (pow_nonneg (norm_nonneg y) _)
          _ ≤ ApmB a ‖z‖ k * ((1 - ‖z‖) / 2) ^ k := by
              refine mul_le_mul_of_nonneg_left ?_ (apmB_nonneg a ha (norm_nonneg z) k)
              exact pow_le_pow_left₀ (norm_nonneg y) hyn.le _
      have hterm : (fun k => FormalMultilinearSeries.ofScalars ℂ (ApmBz a z) k
          (fun _ => y)) = fun k => ApmBz a z k * y ^ k := by
        funext k
        simp [FormalMultilinearSeries.ofScalars_apply_eq]
        exact mul_comm _ _
      rw [hterm]
      have hval : ∑' k, ApmBz a z k * y ^ k = ApmF a (z + y) := by
        rw [funext fun k => (hroweq k).symm, hvalU]
        rfl
      have hhas := hsyz.hasSum
      rwa [hval] at hhas
  exact hball.analyticAt

/-- Summability inside the disk from the radius. -/
private lemma apm_summable_of_radius (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hr : (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius = 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : Summable fun n => a n * ρ ^ n := by
  have hmem : ((ρ : ℂ)) ∈ Metric.eball (0 : ℂ)
      ((FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius) := by
    rw [hr, mem_eball_zero_iff, ← ENNReal.ofReal_one, ← ofReal_norm]
    have hn : ‖(ρ : ℂ)‖ = ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
    rw [hn]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hρ1
  have hq : Summable fun n => (a n : ℂ) * (ρ : ℂ) ^ n :=
    ((FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).summable hmem).congr
      fun n => by
        simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hnorms : ∀ n, ‖(a n : ℂ) * (ρ : ℂ) ^ n‖ = a n * ρ ^ n := by
    intro n
    rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n), abs_of_nonneg hρ0]
  exact (Complex.reCLM.hasSum hq.hasSum).summable.congr fun n => by
    show ((a n : ℂ) * (ρ : ℂ) ^ n).re = _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Radius obstruction from summability beyond 1. -/
private lemma apm_no_summable_beyond (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hr : (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius = 1)
    {ρ : ℝ} (h1 : 1 < ρ) (hs : Summable fun n => a n * ρ ^ n) : False := by
  have hρp : 0 ≤ ρ := by linarith
  have hn : Summable fun n => ‖FormalMultilinearSeries.ofScalars ℂ
      (fun n => (a n : ℂ)) n‖ * ((⟨ρ, hρp⟩ : NNReal) : ℝ) ^ n :=
    hs.congr fun n => by
      rw [FormalMultilinearSeries.ofScalars_norm, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (ha n)]
  have hle := FormalMultilinearSeries.le_radius_of_summable
    (p := FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ)))
    (r := ⟨ρ, hρp⟩) hn
  rw [hr, ENNReal.coe_le_one_iff] at hle
  rw [← NNReal.coe_le_coe] at hle
  simp at hle
  linarith

/-- Tonelli in `ℝ≥0∞`: the total mass identity for nonnegative double arrays. -/
private lemma apm_ennreal_tsum (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hrow : ∀ k, Summable fun n => a (n + k) * ((n + k).choose k : ℝ) * c ^ n) :
    ∑' m, ENNReal.ofReal (a m * (c + t) ^ m)
      = ∑' k, ENNReal.ofReal (ApmB a c k * t ^ k) := by
  let W : ℕ × ℕ → ENNReal := fun p => ENNReal.ofReal (ApmV a c t p)
  have hdiag : ∀ m, (∑' p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m}, W p)
      = ENNReal.ofReal (a m * (c + t) ^ m) := by
    intro m
    rw [tsum_fintype]
    calc
      (∑ p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m}, W (p : ℕ × ℕ)) =
          ENNReal.ofReal (∑ p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m},
          ApmV a c t p) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        exact fun p _ => apmV_nonneg a ha hc ht p
      _ = ENNReal.ofReal (a m * (c + t) ^ m) := by
        congr 1
        rw [← Finset.sum_subtype (Finset.antidiagonal m) (fun _ => Iff.rfl)]
        exact apm_antidiag_sum a c t m
  have htotal : (∑' m, ENNReal.ofReal (a m * (c + t) ^ m)) = ∑' p, W p := by
    rw [← funext hdiag]
    calc
      (∑' m, ∑' p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal m}, W p) =
          ∑' s : Σ m, {p : ℕ × ℕ // p ∈ Finset.antidiagonal m}, W s.2 := by
        symm
        exact ENNReal.tsum_sigma (α := ℕ)
          (β := fun m => {p : ℕ × ℕ // p ∈ Finset.antidiagonal m})
          (fun _ p => W p)
      _ = ∑' p : ℕ × ℕ, W p := Equiv.tsum_eq Finset.sigmaAntidiagonalEquivProd W
  rw [htotal, ENNReal.tsum_prod']
  apply tsum_congr
  intro k
  have hnn : ∀ n, 0 ≤ a (n + k) * ((n + k).choose k : ℝ) * c ^ n := fun n =>
    mul_nonneg (mul_nonneg (ha _) (Nat.cast_nonneg _)) (pow_nonneg hc _)
  rw [ApmB, ENNReal.ofReal_mul (tsum_nonneg hnn),
    ENNReal.ofReal_tsum_of_nonneg hnn (hrow k), ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro n
  change ENNReal.ofReal
      (a (n + k) * ((n + k).choose k : ℝ) * c ^ n * t ^ k) = _
  rw [ENNReal.ofReal_mul (hnn n), ENNReal.ofReal_pow ht]

end ApmCanaries.A00J06.Pringsheim

open ApmCanaries.A00J06.Pringsheim in
theorem apm_a00j06 (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (h_radius : (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius = 1) :
    ¬ ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball 1 r) ∧
      ∀ z ∈ Metric.ball 1 r ∩ Metric.ball 0 1, g z = ∑' n, (a n : ℂ) * z ^ n := by
  rintro ⟨r, hr, g, hg, heq⟩
  let s : ℝ := min (r / 4) (1 / 4)
  let c : ℝ := 1 - s
  let R : ℝ := r / 2
  let t : ℝ := (s + R) / 2
  have hs0 : 0 < s := lt_min (by linarith) (by norm_num)
  have hsr : s < R := by
    dsimp [s, R]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hR0 : 0 < R := by dsimp [R]; linarith
  have hc0 : 0 < c := by
    dsimp [c, s]
    have := min_le_right (r / 4) (1 / 4)
    linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  have hclosed : Metric.closedBall (c : ℂ) (Real.toNNReal R) ⊆ Metric.ball 1 r := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    calc
      dist z 1 ≤ dist z (c : ℂ) + dist (c : ℂ) 1 := dist_triangle _ _ _
      _ ≤ R + s := by
        gcongr
        · simpa [Real.coe_toNNReal R hR0.le] using hz
        · simp [dist_eq_norm, c, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0.le]
      _ < r := by
        dsimp [R, s]
        have := min_le_left (r / 4) (1 / 4)
        linarith
  have hd : DifferentiableOn ℂ g (Metric.closedBall (c : ℂ) (Real.toNNReal R)) := by
    intro z hz
    exact (hg z (hclosed hz)).differentiableAt.differentiableWithinAt
  have hfpsg := hd.hasFPowerSeriesOnBall (show 0 < Real.toNNReal R by exact Real.toNNReal_pos.2 hR0)
  have hsum_mid := apm_summable_of_radius a ha h_radius (by positivity)
    (show (1 + c) / 2 < 1 by linarith)
  have hfpsf := apm_hasFPS a ha hc0 hc1 hsum_mid
  have hev : ∀ᶠ z : ℂ in nhds (c : ℂ), ApmF a z = g z := by
    filter_upwards [Metric.ball_mem_nhds (c : ℂ) hs0,
      Metric.ball_mem_nhds (c : ℂ) hs0] with z hz1 hz0
    symm
    apply heq z
    constructor
    · rw [Metric.mem_ball] at hz1 ⊢
      have hd1 : dist (c : ℂ) 1 = s := by
        simp [c, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0.le]
      calc dist z 1 ≤ dist z (c : ℂ) + dist (c : ℂ) 1 := dist_triangle _ _ _
        _ < s + s := by
          exact add_lt_add_of_lt_of_le hz1 hd1.le
        _ < r := by
          dsimp [s]
          have := min_le_left (r / 4) (1 / 4)
          linarith
    · rw [Metric.mem_ball] at hz0 ⊢
      have hd0 : dist (c : ℂ) 0 = c := by
        rw [dist_zero_right, show (c : ℂ) = (c : ℝ) by rfl, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hc0.le]
      calc dist z 0 ≤ dist z (c : ℂ) + dist (c : ℂ) 0 := dist_triangle _ _ _
        _ < s + c := by
          exact add_lt_add_of_lt_of_le hz0 hd0.le
        _ = 1 := by dsimp [c]; ring
  have hpq := hfpsf.eq_formalMultilinearSeries_of_eventually hfpsg.hasFPowerSeriesAt hev
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htR : t < R := by dsimp [t]; linarith
  have htball : (t : ℂ) ∈ Metric.eball 0 (Real.toNNReal R : ENNReal) := by
    rw [mem_eball_zero_iff]
    calc
      ‖(t : ℂ)‖ₑ = ENNReal.ofReal t := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff hR0).2 htR
      _ = (Real.toNNReal R : ENNReal) := by rfl
  have htball' : (t : ℂ) ∈ Metric.eball 0
      (cauchyPowerSeries g (c : ℂ) (Real.toNNReal R)).radius :=
    Metric.eball_subset_eball hfpsg.r_le htball
  have hBsC := (cauchyPowerSeries g (c : ℂ) (Real.toNNReal R)).summable htball'
  rw [← hpq] at hBsC
  have hBs : Summable fun k => ApmB a c k * t ^ k := by
    have := (Complex.reCLM.hasSum hBsC.hasSum).summable
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, ← Complex.ofReal_pow,
      mul_comm] using this
  have hrow := apmB_summable a ha hc0.le hc1
    (fun ρ hρ0 hρ1 => apm_summable_of_radius a ha h_radius hρ0 hρ1)
  have hmass := apm_ennreal_tsum a ha hc0.le ht0 hrow
  have hrhs : (∑' k, ENNReal.ofReal (ApmB a c k * t ^ k)) ≠ ⊤ :=
    hBs.tsum_ofReal_ne_top
  have hlhs : (∑' m, ENNReal.ofReal (a m * (c + t) ^ m)) ≠ ⊤ := by rwa [hmass]
  have hnn : ∀ m, 0 ≤ a m * (c + t) ^ m := fun m =>
    mul_nonneg (ha m) (pow_nonneg (by dsimp [c, t]; linarith) m)
  have hnnr : Summable fun m => a m * (c + t) ^ m := by
    have he : ∀ m, ENNReal.toNNReal (ENNReal.ofReal (a m * (c + t) ^ m)) =
        ⟨a m * (c + t) ^ m, hnn m⟩ := fun m => by
      apply Subtype.ext
      exact Real.coe_toNNReal _ (hnn m)
    have hsnn := ENNReal.summable_toNNReal_of_tsum_ne_top hlhs
    have hsnn' : Summable fun m => (⟨a m * (c + t) ^ m, hnn m⟩ : NNReal) :=
      hsnn.congr fun m => he m
    exact NNReal.summable_coe.2 hsnn'
  have hgt : 1 < c + t := by dsimp [c, t]; linarith
  exact apm_no_summable_beyond a ha h_radius hgt hnnr
