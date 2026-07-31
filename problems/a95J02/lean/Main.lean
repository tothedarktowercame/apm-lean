/-
! # APM a95J02: Entire function with |f(z)| ≥ |z|^lam and f(1) = 1 must be z^n

f is entire, f(1) = 1, |f(z)| ≥ |z|^lam for all z ∈ ℂ. Then f(z) = z^n
where n = lam (and lam must be a positive integer).

## Proof strategy

1. f has no zeros for z ≠ 0 (since |f(z)| ≥ |z|^lam > 0).
2. f(0) = 0: if not, 1/f is entire and bounded (→0 at ∞), so constant = 0
   by Liouville, contradicting f(1) = 1.
3. Factor f(z) = z^n · g(z) with g entire, g(0) ≠ 0.
4. |g(z)| ≥ |z|^{lam-n}: if lam > n, 1/g bounded → g constant contradiction;
   if lam < n, |g(0)| ≥ ∞ contradiction; so lam = n.
5. With lam = n: |g(z)| ≥ 1, so 1/g bounded → g constant → g = 1 by f(1) = 1.
   Thus f(z) = z^n.

## Theory boundaries

- Liouville's theorem IS in Mathlib (`exists_const_forall_eq_of_bounded`).
- The factoring f(z) = z^n · g(z) from the zero order at 0 needs the
  analytic zero structure API.
- The key step (1/g bounded entire → constant) needs 1/g differentiable,
  which requires g ≠ 0 everywhere, which follows from the bound.

## Statement repair

The generated statement uses `‖z‖ ^ lam` for real lam. In Lean, `‖z‖ : ℝ` and
`^lam` uses `Real.rpow`. This is correct but requires `‖z‖ ≥ 0` for rpow
to be well-defined (which it is, being a norm). We keep the statement.
-/

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Complex Filter Set

noncomputable section

/-- f has no zeros except at the origin.

For z ≠ 0: |f(z)| ≥ |z|^lam > 0 (since |z| > 0 and lam > 0). -/
lemma zero_only_at_origin
    {f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam)
    (hbound : ∀ z : ℂ, ‖z‖ ^ lam ≤ ‖f z‖) :
    ∀ z : ℂ, z ≠ 0 → f z ≠ 0 := by
  intro z hz hzero
  -- |z|^lam ≤ |f(z)| = |0| = 0, but |z|^lam > 0 for z ≠ 0, contradiction.
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrpow_pos : 0 < ‖z‖ ^ lam := Real.rpow_pos_of_pos hnorm_pos lam
  have hfbound : ‖z‖ ^ lam ≤ ‖f z‖ := hbound z
  rw [hzero, norm_zero] at hfbound
  linarith

/-- f(0) = 0.

If f(0) ≠ 0, then f has no zeros (by zero_only_at_origin + f(0) ≠ 0),
so 1/f is entire. And |1/f(z)| ≤ 1/|z|^lam → 0 as |z| → ∞.
By Liouville, 1/f is constant = c. Since |1/f(z)| → 0, c = 0,
contradicting 1/f(1) = 1/f(1) = 1 (since f(1) = 1).

**Blocker:** This requires constructing 1/f as a differentiable function
and showing it's bounded, then applying Liouville. The construction of
1/f from f ≠ 0 everywhere is available via `Differentiable.inv`, and
Liouville is available, but the boundedness argument (1/|z|^lam → 0)
requires showing the range of 1/f is bounded — which needs the
rpow → 0 at ∞ limit. -/
lemma f_zero_eq_zero
    {f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam)
    (hf : Differentiable ℂ f)
    (hf1 : f 1 = 1)
    (hbound : ∀ z : ℂ, ‖z‖ ^ lam ≤ ‖f z‖) :
    f 0 = 0 := by
  by_contra hf0
  have hne : ∀ z, f z ≠ 0 := by
    intro z
    by_cases hz : z = 0
    · simpa [hz] using hf0
    · exact zero_only_at_origin hlam hbound z hz
  have hinv_diff : Differentiable ℂ (f⁻¹) := hf.inv hne
  have hinv_norm :
      Tendsto (fun z : ℂ => ‖(f z)⁻¹‖) (cocompact ℂ) (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      _ ((tendsto_rpow_neg_atTop hlam).comp tendsto_norm_cocompact_atTop)
    filter_upwards [((tendsto_norm_cocompact_atTop :
      Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop).eventually (eventually_gt_atTop 0))]
      with z hz
    simp only [Function.comp_apply, norm_inv]
    rw [Real.rpow_neg hz.le]
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hne z)) (Real.rpow_pos_of_pos hz lam)).2 (hbound z)
  have hinv_tendsto : Tendsto (f⁻¹) (cocompact ℂ) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Pi.inv_apply] using hinv_norm
  have hconst := hinv_diff.eq_const_of_tendsto_cocompact hinv_tendsto
  have := congrFun hconst 1
  simp [hf1] at this

/-- The quotient `zⁿ / f z`, filled in at a zero using the local analytic
factor of `f`, has a removable singularity. -/
lemma normalizedQuotient_differentiable
    {f g : ℂ → ℂ} {n : ℕ}
    (hf : Differentiable ℂ f)
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 ≠ 0)
    (hfg : f =ᶠ[nhds 0] fun z => z ^ n * g z)
    (hzero : ∀ z, z ≠ 0 → f z ≠ 0) :
    Differentiable ℂ (fun z => if z = 0 then (g 0)⁻¹ else z ^ n / f z) := by
  intro z
  by_cases hz : z = 0
  · subst z
    apply (hg.differentiableAt.inv hg0).congr_of_eventuallyEq
    filter_upwards [hfg, hg.continuousAt.eventually_ne hg0] with z hfz hgz
    by_cases hz : z = 0
    · simp [hz]
    · simp only [hz, ↓reduceIte, Pi.inv_apply]
      rw [hfz]
      field_simp
  · apply ((differentiableAt_pow n).div (hf z) (hzero z hz)).congr_of_eventuallyEq
    filter_upwards [continuousAt_id.eventually_ne hz] with w hw
    change w ≠ 0 at hw
    simp [hw]

/-- Main theorem: f(z) = z^n where n = lam (lam is a positive integer).

Combines: f(0) = 0 → factor out z^n → g bounded → Liouville → g = 1. -/
theorem entire_lower_bound_is_monomial
    {f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam)
    (hf : Differentiable ℂ f)
    (hf1 : f 1 = 1)
    (hbound : ∀ z : ℂ, ‖z‖ ^ lam ≤ ‖f z‖) :
    ∃ n : ℕ, 0 < n ∧ (lam = ↑n) ∧ ∀ z, f z = z ^ n := by
  have hf0 := f_zero_eq_zero hlam hf hf1 hbound
  have hfa : AnalyticAt ℂ f 0 := hf.analyticAt 0
  have horder_ne_top : analyticOrderAt f 0 ≠ ⊤ := by
    rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 (fun z => hf.analyticAt z)]
    intro h
    have := congrFun h 1
    simp [hf1] at this
  let n := analyticOrderNatAt f 0
  obtain ⟨g, hg, hg0, hfg'⟩ := hfa.analyticOrderAt_ne_top.mp horder_ne_top
  have hfg : f =ᶠ[nhds 0] fun z => z ^ n * g z := by
    simpa only [n, sub_zero, smul_eq_mul] using hfg'
  have hn : 0 < n := by
    have hfg0 := hfg.self_of_nhds
    rw [hf0] at hfg0
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    simp [this] at hfg0
    exact hg0 hfg0.symm
  have hzero : ∀ z, z ≠ 0 → f z ≠ 0 := zero_only_at_origin hlam hbound
  let G : ℂ → ℂ := fun z => if z = 0 then (g 0)⁻¹ else z ^ n / f z
  have hGdiff : Differentiable ℂ G :=
    normalizedQuotient_differentiable hf hg hg0 hfg hzero
  have hG1 : G 1 = 1 := by simp [G, hf1]
  have hGbound : ∀ z, z ≠ 0 → ‖G z‖ ≤ ‖z‖ ^ ((n : ℝ) - lam) := by
    intro z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    dsimp [G]
    rw [if_neg hz, norm_div, norm_pow, ← Real.rpow_natCast]
    rw [Real.rpow_sub hzpos]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hzpos.le _) (Real.rpow_pos_of_pos hzpos lam)
      (hbound z)
  have hlam_le_n : lam ≤ (n : ℝ) := by
    by_contra hle
    have hpos : 0 < lam - (n : ℝ) := sub_pos.mpr (lt_of_not_ge hle)
    have hGtendsto : Tendsto G (cocompact ℂ) (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        _ ((tendsto_rpow_neg_atTop hpos).comp tendsto_norm_cocompact_atTop)
      filter_upwards [((tendsto_norm_cocompact_atTop :
        Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop).eventually
          (eventually_gt_atTop 0))] with z hz
      change ‖G z‖ ≤ ((fun x : ℝ => x ^ (-(lam - (n : ℝ)))) ∘ norm) z
      simpa only [Function.comp_apply, neg_sub] using hGbound z (norm_pos_iff.mp hz)
    have hconst := hGdiff.eq_const_of_tendsto_cocompact hGtendsto
    have := congrFun hconst 1
    rw [hG1] at this
    simp at this
  have hn_le_lam : (n : ℝ) ≤ lam := by
    by_contra hle
    have hpos : 0 < (n : ℝ) - lam := sub_pos.mpr (lt_of_not_ge hle)
    have hrpow :
        Tendsto (fun z : ℂ => ‖z‖ ^ ((n : ℝ) - lam))
          (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have h :=
        (Real.continuousAt_rpow_const 0 ((n : ℝ) - lam) (.inr hpos.le)).continuousWithinAt.tendsto.comp
          (tendsto_norm_nhdsNE_zero (E := ℂ))
      simpa [Real.zero_rpow hpos.ne'] using h
    have hGnorm :
        Tendsto (fun z : ℂ => ‖G z‖) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        _ hrpow
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hGbound z hz
    have hGnorm_cont :
        Tendsto (fun z : ℂ => ‖G z‖) (nhdsWithin 0 {0}ᶜ) (nhds ‖G 0‖) :=
      (hGdiff.continuous.norm.continuousAt.tendsto).mono_left inf_le_left
    have hG0norm : ‖G 0‖ = 0 := tendsto_nhds_unique hGnorm_cont hGnorm
    have hG0ne : G 0 ≠ 0 := by
      dsimp [G]
      simpa using inv_ne_zero hg0
    exact hG0ne (norm_eq_zero.mp hG0norm)
  have hlam_eq : lam = (n : ℝ) := le_antisymm hlam_le_n hn_le_lam
  have hGbounded : Bornology.IsBounded (range G) := by
    apply (Metric.isBounded_closedBall :
      Bornology.IsBounded (Metric.closedBall (0 : ℂ) (max ‖G 0‖ 1))).subset
    rintro _ ⟨z, rfl⟩
    rw [mem_closedBall_zero_iff]
    by_cases hz : z = 0
    · subst z
      exact le_max_left _ _
    · calc
        ‖G z‖ ≤ ‖z‖ ^ ((n : ℝ) - lam) := hGbound z hz
        _ = 1 := by rw [hlam_eq, sub_self, Real.rpow_zero]
        _ ≤ max ‖G 0‖ 1 := le_max_right _ _
  have hGconst : ∀ z, G z = 1 := by
    intro z
    calc
      G z = G 1 := hGdiff.apply_eq_apply_of_bounded hGbounded z 1
      _ = 1 := hG1
  refine ⟨n, hn, hlam_eq, fun z => ?_⟩
  by_cases hz : z = 0
  · subst z
    simp [hf0, hn.ne']
  · have hq := hGconst z
    dsimp [G] at hq
    rw [if_neg hz] at hq
    apply (div_eq_one_iff_eq (hzero z hz)).mp hq |>.symm

end
