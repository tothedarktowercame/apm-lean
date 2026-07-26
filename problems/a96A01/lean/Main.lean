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

/-- (a) ‖f‖_p ≤ ‖f‖_q when 0 < p < q ≤ 1.

**Blocker:** Requires Hölder's inequality with exponents q/p > 1 and
its conjugate, applied to |f|^p · 1 on [0,1]. Mathlib has Hölder
(`norm_integral_mul_le`) but the specific application to this
quasi-norm setup needs assembly. -/
theorem quasiNorm_antitone
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    quasiNorm f p ≤ quasiNorm f q := by
  sorry

/-- The limit L = lim_{p→0⁺} ‖f‖_p exists.

Since p ↦ ‖f‖_p is decreasing (part a) and bounded below by 0,
the limit exists by the monotone convergence theorem for functions. -/
theorem quasiNorm_tendsto_exists
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume) :
    ∃ L : ℝ, Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  sorry

/-- (b) L > 0 implies |f| > 0 a.e.

**Blocker:** Requires DCT: |f|^p → 1_{f≠0} as p → 0⁺, dominated by 1+|f|. -/
theorem ae_pos_of_limit_pos
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    {L : ℝ} (hL : 0 < L)
    (hLim : Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖ := by
  sorry

/-- (c) L ≥ exp(∫ log|f|).

**Blocker:** Requires Jensen for the convex function exp:
∫e^{p·log|f|} ≥ e^{p·∫log|f|}, then take log and p → 0. -/
theorem limit_ge_geometric_mean
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    (hf_pos : ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖)
    {L : ℝ} (hL : 0 < L)
    (hLim : Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    exp (∫ x in Set.Icc (0:ℝ) 1, log ‖f x‖ ∂volume) ≤ L := by
  sorry

end
