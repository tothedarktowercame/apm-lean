import Mathlib

/-!
# APM a97J04: Local absolute continuity at a boundary point

## Statement repairs

None.

## Encoding questions

None. A function on `[0,1]` is represented by an ambient `f : ℝ → ℝ` whose
hypotheses and conclusion are all restricted to the stated intervals. Bounded
variation and absolute continuity use Mathlib's `BoundedVariationOn` and
`AbsolutelyContinuousOnInterval` predicates directly.
-/

open Set Topology Filter MeasureTheory

theorem apm_a97j04
    (f : ℝ → ℝ)
    (hcontinuous : ContinuousOn f (Icc (0 : ℝ) 1))
    (hvariation : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hlocal : ∀ δ : ℝ, 0 < δ → δ < 1 →
      AbsolutelyContinuousOnInterval f δ 1) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  -- Strategy from a93J01 (same problem): define g(x) = f(0) + ∫₀ˣ f'(t)dt.
  -- Show g is AC on [0,1] (integral of integrable function is AC).
  -- Show f = g on [0,1] (using local AC + continuity + sequence argument).
  -- Then f is AC since f = g and g is AC.
  -- -- (Memory: e-codexpilot-extend-local-absolute-continuity-to-an-endpoint-via-the-derivative-primitive)
  -- --    Prior attempt at this exact problem via the FTC route.
  have h_deriv : IntervalIntegrable (deriv f) volume 0 1 :=
    (show BoundedVariationOn f (uIcc 0 1) from by
      simpa [uIcc_of_le] using hvariation).intervalIntegrable_deriv
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
    let a := fun n : ℕ => x / n
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
      (hcontinuous 0 (by simp)).tendsto.comp ha_tendsto_within
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
        (hlocal (a n) ha_pos ha_lt_one).mono (by
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

#print axioms apm_a97j04
