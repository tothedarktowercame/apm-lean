import Mathlib

open MeasureTheory

def apm_m96j02_LocallyLipschitzInSecond (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R →
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ t u v : ℝ,
        |t| ≤ R → |u| ≤ R → |v| ≤ R →
          |g t u - g t v| ≤ L * |u - v|

lemma apm_m96j02_continuousOn_comp_graph
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    {T : ℝ} {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T)) :
    ContinuousOn (fun t => g t (y t)) (Set.Icc 0 T) := by
  exact hg.comp_continuousOn (continuousOn_id.prodMk hy)

lemma apm_m96j02_intervalIntegrable_comp_graph
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    {T : ℝ} (hT : 0 ≤ T) {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T)) :
    IntervalIntegrable (fun t => g t (y t)) volume 0 T := by
  have hc := apm_m96j02_continuousOn_comp_graph g hg hy
  rw [← Set.uIcc_of_le hT] at hc
  exact hc.intervalIntegrable

/-- Taylor's formula with integral remainder, expressed using the same
within-derivatives as the repaired closed-interval statement. -/
theorem apm_m96j02_ivp_to_volterra
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (α β T : ℝ) (hT : 0 ≤ T) (x : ℝ → ℝ)
    (hx : ContDiffOn ℝ 2 x (Set.Icc 0 T))
    (hx0 : x 0 = α)
    (hxd0 : derivWithin x (Set.Icc 0 T) 0 = β)
    (hxode : ∀ t ∈ Set.Icc (0 : ℝ) T,
      derivWithin (derivWithin x (Set.Icc 0 T)) (Set.Icc 0 T) t =
        g t (x t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      x t = (∫ s in (0 : ℝ)..t, (t - s) * g s (x s)) + α + β * t := by
  intro t ht
  rcases hT.eq_or_lt with rfl | hT
  · simp only [Set.Icc_self, Set.mem_singleton_iff] at ht
    subst t
    simp [hx0]
  let S : Set ℝ := Set.Icc 0 T
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_Icc hT
  have hd : ContDiffOn ℝ 1 (derivWithin x S) S := by
    exact hx.derivWithin hS (by norm_num)
  have hxt : 0 ≤ t := ht.1
  have hsub : Set.Icc 0 t ⊆ S := by
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hx_int :
      (∫ s in (0 : ℝ)..t, derivWithin x S s) = x t - x 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hxt
      (hx.continuousOn.mono hsub)
    · intro s hs
      have hsS : s ∈ S := hsub ⟨hs.1.le, hs.2.le⟩
      have hh : HasDerivWithinAt x (derivWithin x S s) S s :=
        ((hx s hsS).differentiableWithinAt (by norm_num)).hasDerivWithinAt
      exact (hh.hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))).hasDerivWithinAt
    · exact (hd.continuousOn.mono hsub).intervalIntegrable_of_Icc hxt
  have hforce : ContinuousOn (fun s => g s (x s)) (Set.Icc 0 t) :=
    (apm_m96j02_continuousOn_comp_graph g hg hx.continuousOn).mono hsub
  have hv_int : IntervalIntegrable (fun s => g s (x s)) volume 0 t :=
    hforce.intervalIntegrable_of_Icc hxt
  have hv_deriv : ∀ s ∈ Set.Icc 0 t,
      HasDerivWithinAt (derivWithin x S) (g s (x s)) (Set.Icc 0 t) s := by
    intro s hs
    have hsS : s ∈ S := hsub hs
    have hdif := (hd s hsS).differentiableWithinAt (by norm_num)
    have hh : HasDerivWithinAt (derivWithin x S)
        (derivWithin (derivWithin x S) S s) S s :=
      hdif.hasDerivWithinAt
    rw [hxode s hsS] at hh
    exact hh.mono hsub
  have hu_deriv : ∀ s ∈ Set.Icc 0 t,
      HasDerivWithinAt (fun r : ℝ => t - r) (-1) (Set.Icc 0 t) s := by
    intro s hs
    convert (hasDerivAt_const s t).sub (hasDerivAt_id s) |>.hasDerivWithinAt using 1 <;>
      simp
  have hu_int : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume 0 t :=
    intervalIntegrable_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := 0) (b := t) (u := fun r : ℝ => t - r)
    (v := derivWithin x S) (u' := fun _ => -1)
    (v' := fun s => g s (x s))
    (by simpa [Set.uIcc_of_le hxt] using hu_deriv)
    (by simpa [Set.uIcc_of_le hxt] using hv_deriv) hu_int hv_int
  simp only [sub_self, zero_mul, sub_zero] at hibp
  simp only [neg_one_mul, intervalIntegral.integral_neg, sub_neg_eq_add] at hibp
  change derivWithin x S 0 = β at hxd0
  rw [hibp, hx_int, hx0, hxd0]
  ring

/-- The a-priori box estimate and contraction argument for two continuous
fixed points of the Volterra operator. -/
theorem apm_m96j02_local_volterra_uniqueness
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (hLip : apm_m96j02_LocallyLipschitzInSecond g)
    (α β : ℝ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (x y : ℝ → ℝ),
        ContinuousOn x (Set.Icc 0 T) →
        ContinuousOn y (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          x t = (∫ s in (0 : ℝ)..t, (t - s) * g s (x s)) + α + β * t) →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          y t = (∫ s in (0 : ℝ)..t, (t - s) * g s (y s)) + α + β * t) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, x t = y t := by
  sorry

theorem apm_m96j02
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (hLip : apm_m96j02_LocallyLipschitzInSecond g)
    (α β : ℝ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (x y : ℝ → ℝ),
        ContDiffOn ℝ 2 x (Set.Icc 0 T) →
        x 0 = α → derivWithin x (Set.Icc 0 T) 0 = β →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          derivWithin (derivWithin x (Set.Icc 0 T)) (Set.Icc 0 T) t =
            g t (x t)) →
        ContinuousOn y (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          y t = (∫ s in (0 : ℝ)..t, (t - s) * g s (y s)) + α + β * t) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, x t = y t := by
  obtain ⟨T, hT, huniq⟩ :=
    apm_m96j02_local_volterra_uniqueness g hg hLip α β
  refine ⟨T, hT, ?_⟩
  intro x y hx hx0 hxd0 hxode hy hyvolterra
  exact huniq x y hx.continuousOn hy
    (apm_m96j02_ivp_to_volterra g hg α β T hT.le x hx hx0 hxd0 hxode)
    hyvolterra

#print axioms apm_m96j02
