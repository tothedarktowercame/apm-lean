import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# APM a93J01: Continuous + BV + AC on [a,1] for all a > 0 ⟹ AC on [0,1]

**Problem.** Let f : [0,1] → ℝ be continuous, of bounded variation, and
absolutely continuous on [a,1] for all 0 < a < 1. Prove f is AC on [0,1].

## Proof

BV gives V(f, [0,a]) → 0 as a → 0⁺ (by `tendsto_eVariationOn_Icc_zero_left`).
Choose a₀ with V(f, [0,a₀]) < ε/2. Use AC on [a₀,1] to get δ > 0.
For any disjoint intervals with Σ(bᵢ-aᵢ) < min(δ, a₀):
- Intervals with aᵢ < a₀: total oscillation ≤ V(f, [0, 2a₀]) < ε/2
- Intervals with aᵢ ≥ a₀: handled by AC on [a₀,1], sum < ε/2
Total < ε.

## Statement repair note

Uses Mathlib's `AbsolutelyContinuousOnInterval` for AC, `BoundedVariationOn`
for BV, and `eVariationOn` for total variation. The informal proof's
custom `AbsolutelyContinuousOn` is replaced by Mathlib's definition.
-/

set_option linter.unusedVariables false in
noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace ApmCanaries.A93J01

/-- **Main theorem:** continuous + BV + AC on [a,1] for all 0 < a < 1
    implies AC on [0,1].

    BV makes `deriv f` interval-integrable. Its indefinite integral is AC;
    the fundamental theorem on each `[a,1]`, followed by `a = x / n → 0`,
    shows that this integral agrees with `f - f 0` on `[0,1]`. Continuity
    supplies the equality at the left endpoint. -/
theorem ac_on_01_of_continuous_bv_ac_from_a
    {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc (0:ℝ) 1))
    (hBV : BoundedVariationOn f (Icc (0:ℝ) 1))
    (hAC : ∀ a : ℝ, 0 < a → a < 1 → AbsolutelyContinuousOnInterval f a 1) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  have h_deriv : IntervalIntegrable (deriv f) volume 0 1 :=
    (show BoundedVariationOn f (uIcc 0 1) from by
      simpa [uIcc_of_le] using hBV).intervalIntegrable_deriv
  let g := fun x : ℝ => f 0 + ∫ t in 0..x, deriv f t
  have h_integral_ac :
      AbsolutelyContinuousOnInterval (fun x => ∫ t in 0..x, deriv f t) 0 1 :=
    h_deriv.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have h_const_ac : AbsolutelyContinuousOnInterval (fun _ : ℝ => f 0) 0 1 :=
    (LipschitzWith.const (α := ℝ) (f 0)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hg_ac : AbsolutelyContinuousOnInterval g 0 1 := by
    simpa only [g, Pi.add_apply] using h_const_ac.add h_integral_ac
  have hfg : ∀ x ∈ Icc (0 : ℝ) 1, f x = g x := by
    intro x hx
    rcases hx with ⟨hx₀, hx₁⟩
    rcases hx₀.eq_or_lt with rfl | hxpos
    · simp [g]
    let a : ℕ → ℝ := fun n => x / n
    have ha_tendsto : Tendsto a atTop (𝓝 0) := by
      simpa only [a] using tendsto_const_div_atTop_nhds_zero_nat x
    have ha_mem : ∀ᶠ n in atTop, a n ∈ Icc (0 : ℝ) 1 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      constructor
      · exact div_nonneg hxpos.le hnpos.le
      · exact (div_le_self hxpos.le (by exact_mod_cast hn)).trans hx₁
    have ha_tendsto_within : Tendsto a atTop (𝓝[Icc (0 : ℝ) 1] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨ha_tendsto, ha_mem⟩
    have hf_tendsto : Tendsto (fun n => f (a n)) atTop (𝓝 (f 0)) :=
      (hcont 0 (by simp)).tendsto.comp ha_tendsto_within
    have hg_tendsto : Tendsto (fun n => g (a n)) atTop (𝓝 (g 0)) :=
      (hg_ac.continuousOn 0 (by simp)).tendsto.comp
        (by simpa [uIcc_of_le] using ha_tendsto_within)
    have hsub_tendsto :
        Tendsto (fun n => f (a n) - g (a n)) atTop (𝓝 (f 0 - g 0)) :=
      hf_tendsto.sub hg_tendsto
    have hsub_eventually : ∀ᶠ n in atTop, f (a n) - g (a n) = f x - g x := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hn_gt_one : (1 : ℝ) < n := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < n := zero_lt_one.trans hn_gt_one
      have ha_pos : 0 < a n := div_pos hxpos hnpos
      have ha_lt_x : a n < x := div_lt_self hxpos hn_gt_one
      have ha_lt_one : a n < 1 := ha_lt_x.trans_le hx₁
      have hlocal : AbsolutelyContinuousOnInterval f (a n) x :=
        (hAC (a n) ha_pos ha_lt_one).mono (by
          simpa [uIcc_of_le, ha_lt_x.le, ha_lt_one.le] using
            (Icc_subset_Icc_right hx₁ : Icc (a n) x ⊆ Icc (a n) 1))
      have hftc : ∫ t in a n..x, deriv f t = f x - f (a n) :=
        hlocal.integral_deriv_eq_sub
      have h0a : IntervalIntegrable (deriv f) volume 0 (a n) :=
        h_deriv.mono_set (by
          simpa [uIcc_of_le, ha_pos.le] using
            (Icc_subset_Icc_right (ha_lt_x.le.trans hx₁) :
              Icc 0 (a n) ⊆ Icc 0 1))
      have hax : IntervalIntegrable (deriv f) volume (a n) x :=
        h_deriv.mono_set (by
          simpa [uIcc_of_le, ha_lt_x.le] using
            (Icc_subset_Icc ha_pos.le hx₁ : Icc (a n) x ⊆ Icc 0 1))
      have hadd :
          (∫ t in 0..a n, deriv f t) + ∫ t in a n..x, deriv f t =
            ∫ t in 0..x, deriv f t :=
        intervalIntegral.integral_add_adjacent_intervals h0a hax
      dsimp only [g]
      linarith
    have hconst_tendsto :
        Tendsto (fun _ : ℕ => f x - g x) atTop (𝓝 (f 0 - g 0)) :=
      hsub_tendsto.congr' hsub_eventually
    have hsub_eq : f x - g x = f 0 - g 0 :=
      (tendsto_nhds_unique hconst_tendsto
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => f x - g x) atTop (𝓝 (f x - g x)))).symm
    simp only [g, intervalIntegral.integral_same, add_zero, sub_self] at hsub_eq
    exact sub_eq_zero.mp hsub_eq
  rw [absolutelyContinuousOnInterval_iff] at hg_ac ⊢
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ := hg_ac ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  convert hgδ E hE hlen using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfg _ (by simpa [uIcc_of_le] using (hE.1 i hi).1),
    hfg _ (by simpa [uIcc_of_le] using (hE.1 i hi).2)]

end ApmCanaries.A93J01
