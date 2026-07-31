/-
! # APM a96A01: Lp quasi-norms for 0 < p ≤ 1, monotonicity, and geometric mean limit

(a) ‖f‖_p ≤ ‖f‖_q when 0 < p < q ≤ 1 (antitone in p), so L = lim_{p→0⁺} ‖f‖_p exists.
(b) L > 0 implies |f| > 0 a.e.
(c) L ≥ exp(∫ log|f|).

## Proof strategy

(a) Hölder on |f|^p · 1 with exponents q/p and its conjugate.
(b) t^p ≤ 1+t gives dominated convergence: ∫|f|^p → m({f≠0}).
(c) Jensen for convex exp: ∫e^{p log|f|} ≥ e^{p ∫log|f|}.

## Theory boundaries

- Hölder's inequality IS in Mathlib but needs adaptation for 0 < p < 1.
- Jensen for integrals (ConvexOn) IS in Mathlib.
- The dominated convergence theorem IS in Mathlib.
- The limit computation p → 0 requires filter-based arguments.
- The hint t^p ≤ 1+t is a tractable calculus lemma.

## Statement repair

Used Mathlib's `MemLp` (not `Memℒp`). The `quasiNorm` uses interval integral
on [0,1]. Variable `μ` changed to `volume.restrict (Icc 0 1)` directly.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory Set Filter Real Topology

open scoped ENNReal

noncomputable section

/-- The Lp quasi-norm for 0 < p: (∫₀¹ |f|^p)^{1/p}. -/
def quasiNorm (f : ℝ → ℝ) (p : ℝ) : ℝ :=
  (∫ x in Set.Icc (0:ℝ) 1, ‖f x‖ ^ p ∂volume) ^ (1 / p)

/-- The hint: t^p ≤ 1 + t for t ≥ 0 and 0 < p ≤ 1.

This follows from the concavity of x ↦ x^p for 0 < p < 1:
x^p is concave with x^p(0) = 0, x^p(1) = 1, so x^p ≤ (1-0)·1 + 0 = 1
for x ∈ [0,1]. For x ≥ 1: x^p ≤ x (since p ≤ 1).
So x^p ≤ max(1, x) ≤ 1 + x for all x ≥ 0. -/
lemma rpow_le_one_add {t : ℝ} (ht : 0 ≤ t) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    t ^ p ≤ 1 + t := by
  by_cases h1 : t ≤ 1
  · -- For t ∈ [0,1]: t^p ≤ 1 since p > 0 and 0 ≤ t ≤ 1.
    have : t ^ p ≤ 1 := Real.rpow_le_one ht h1 hp.le
    linarith
  · -- For t > 1: t^p ≤ t^1 = t since p ≤ 1 and t ≥ 1.
    have htt : t ^ (1 : ℝ) = t := rpow_one t
    have : t ^ p ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hp1
    rw [htt] at this
    linarith

/-- On the unit interval, `quasiNorm` is Mathlib's real-valued `Lᵖ`
seminorm. -/
lemma quasiNorm_eq_lpNorm
    {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume)
    {p : ℝ} (hp : 0 < p) :
    quasiNorm f p =
      lpNorm f (ENNReal.ofReal p) (volume.restrict (Icc 0 1)) := by
  have hmeas : AEStronglyMeasurable f (volume.restrict (Icc 0 1)) :=
    hf.aestronglyMeasurable
  rw [quasiNorm,
    lpNorm_eq_integral_norm_rpow_toReal
      (by positivity)
      (by simp) hmeas]
  simp [ENNReal.toReal_ofReal hp.le]

/-- (a) ‖f‖_p ≤ ‖f‖_q when 0 < p < q ≤ 1.

This is the probability-space exponent comparison for `Lᵖ` seminorms,
transported through `quasiNorm_eq_lpNorm`. -/
theorem quasiNorm_antitone
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    quasiNorm f p ≤ quasiNorm f q := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by
    simp [μ, Real.volume_Icc]⟩
  have hmeas : AEStronglyMeasurable f μ := by
    simpa [μ] using hf.aestronglyMeasurable
  have hq0 : 0 < q := hp.trans hpq
  have hpq' : ENNReal.ofReal p ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal hpq.le
  have hq_mem : MemLp f (ENNReal.ofReal q) μ := by
    have hf_one : MemLp f 1 μ := by
      rw [memLp_one_iff_integrable]
      simpa [μ] using hf
    exact hf_one.mono_exponent (by
      simpa using ENNReal.ofReal_le_ofReal hq)
  rw [quasiNorm_eq_lpNorm hf hp, quasiNorm_eq_lpNorm hf hq0,
    ← toReal_eLpNorm hmeas, ← toReal_eLpNorm hmeas]
  exact ENNReal.toReal_mono hq_mem.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hpq' hmeas)

/-- The limit L = lim_{p→0⁺} ‖f‖_p exists.

Since `p ↦ ‖f‖_p` is monotone on `(0,1)` and bounded below by zero,
the order-topology right-limit theorem applies. -/
theorem quasiNorm_tendsto_exists
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume) :
    ∃ L : ℝ, Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  have hmono : MonotoneOn (quasiNorm f) (Ioo (0 : ℝ) 1) := by
    intro p hp' q hq' hpq'
    rcases hpq'.eq_or_lt with rfl | hpq'
    · exact le_rfl
    · exact quasiNorm_antitone hf hp'.1 hpq' hq'.2.le
  have hbdd : BddBelow (quasiNorm f '' Ioo (0 : ℝ) 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, hp', rfl⟩
    apply Real.rpow_nonneg
    exact integral_nonneg_of_ae
      (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact ⟨sInf (quasiNorm f '' Ioo (0 : ℝ) 1),
    MonotoneOn.tendsto_nhdsWithin_Ioo_right
      ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ hmono hbdd⟩

/-- (b) L > 0 implies |f| > 0 a.e.

**Remaining construction:** DCT gives
`∫ |f|^p → volume {x | f x ≠ 0}`.  If the zero set has positive measure,
the latter is strictly below one, and raising an eventual bound `< 1` to
`1 / p → ∞` forces `quasiNorm f p → 0`, contradicting `L > 0`. -/
theorem ae_pos_of_limit_pos
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    {L : ℝ} (hL : 0 < L)
    (hLim : Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖ := by
  sorry

/-- (c) L ≥ exp(∫ log|f|).

**Remaining construction:** first derive integrability of `log ‖f‖` from
`L > 0` (its positive part is controlled by `f`; a nonintegrable negative
part would force the quasi-norm limit to zero).  Jensen for `exp` then gives
the inequality at each positive exponent, and `hLim` supplies the limit. -/
theorem limit_ge_geometric_mean
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    (hf_pos : ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖)
    {L : ℝ} (hL : 0 < L)
    (hLim : Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    exp (∫ x in Set.Icc (0:ℝ) 1, log ‖f x‖ ∂volume) ≤ L := by
  sorry

end
