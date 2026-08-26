import Mathlib

/-!
# APM a97J07

## Statement repairs

None.

## Encoding questions

None. Analyticity on the open disk is encoded as complex differentiability
there, and the two boundary estimates retain the source's strict upper- and
lower-semicircle hypotheses.
-/

open Complex Metric Set Filter

theorem apm_a97j07 (f : ℂ → ℂ) (a b : ℝ)
    (hf_cont : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hf_analytic : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (ha : ∀ z ∈ sphere (0 : ℂ) 1, 0 < z.im → ‖f z‖ ≤ a)
    (hb : ∀ z ∈ sphere (0 : ℂ) 1, z.im < 0 → ‖f z‖ ≤ b) :
    ‖f 0‖ ≤ Real.sqrt (a * b) := by
  let g : ℂ → ℂ := fun z ↦ f z * f (-z)
  have hneg_ball : MapsTo (fun z : ℂ ↦ -z) (ball 0 1) (ball 0 1) := by
    intro z hz
    simpa [mem_ball_zero_iff] using hz
  have hg_diff : DifferentiableOn ℂ g (ball 0 1) := by
    apply hf_analytic.mul
    simpa [Function.comp_def] using
      hf_analytic.comp differentiable_neg.differentiableOn hneg_ball
  have hneg_closed : MapsTo (fun z : ℂ ↦ -z) (closedBall 0 1) (closedBall 0 1) := by
    intro z hz
    simpa [mem_closedBall_zero_iff] using hz
  have hg_cont : ContinuousOn g (closedBall 0 1) := by
    exact hf_cont.mul (by
      simpa [Function.comp_def] using
        (hf_cont.comp continuous_neg.continuousOn hneg_closed))
  have hg_dc : DiffContOnCl ℂ g (ball 0 1) :=
    ⟨hg_diff, by simpa [closure_ball] using hg_cont⟩
  have hfront : ∀ z ∈ frontier (ball (0 : ℂ) 1), ‖g z‖ ≤ a * b := by
    intro z hz
    have hzs : z ∈ sphere (0 : ℂ) 1 := by simpa [frontier_ball] using hz
    have hnzs : -z ∈ sphere (0 : ℂ) 1 := by simpa [mem_sphere] using hzs
    rw [show g z = f z * f (-z) by rfl, norm_mul]
    rcases lt_trichotomy z.im 0 with hminus | haxis | hplus
    · rw [mul_comm]
      exact mul_le_mul (ha (-z) hnzs (by simpa using hminus)) (hb z hzs hminus)
        (norm_nonneg _) (le_trans (norm_nonneg _) (ha (-z) hnzs (by simpa using hminus)))
    · have hzpm : z = 1 ∨ z = -1 := by
        have hn : ‖z‖ = 1 := by simpa [mem_sphere] using hzs
        rw [Complex.norm_def, Complex.normSq_apply, haxis] at hn
        simp only [zero_mul, add_zero] at hn
        rw [← pow_two, Real.sqrt_sq_eq_abs] at hn
        rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hn with hre | hre
        · left; apply Complex.ext <;> simp [hre, haxis]
        · right; apply Complex.ext <;> simp [hre, haxis]
      rcases hzpm with rfl | rfl
      · let u : ℕ → ℂ := fun n ↦
          Complex.exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
        have ht : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hc : Tendsto (fun n : ℕ ↦ ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
            atTop (nhds 0) := by
          simpa [Function.comp_def] using
            (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).mul
              (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ Complex.I) atTop (nhds Complex.I))
        have hu : Tendsto u atTop (nhds 1) := by
          simpa [u] using Complex.continuous_exp.continuousAt.tendsto.comp hc
        have hu_closed : ∀ n, u n ∈ closedBall (0 : ℂ) 1 := by
          intro n
          rw [mem_closedBall]
          simp [dist_zero_right, u, Complex.norm_exp]
        have hlim : Tendsto (fun n ↦ ‖g (u n)‖) atTop (nhds ‖g 1‖) :=
          ((hg_cont 1 (by simp [mem_closedBall])).tendsto.comp
            (tendsto_nhdsWithin_iff.mpr
              ⟨hu, Filter.Eventually.of_forall hu_closed⟩)).norm
        have hend : ‖g 1‖ ≤ a * b := le_of_tendsto hlim (by
          filter_upwards with (n : ℕ)
          have hθpos : 0 < (1 / ((n : ℝ) + 1)) := one_div_pos.mpr (by positivity)
          have hθpi : (1 / ((n : ℝ) + 1)) < Real.pi :=
            lt_of_le_of_lt ((div_le_one (by positivity)).2 (by norm_num))
              (lt_trans (by norm_num) Real.pi_gt_three)
          have hus : u n ∈ sphere (0 : ℂ) 1 := by simp [u, Complex.norm_exp]
          have huim : 0 < (u n).im := by
            simp only [u]
            rw [Complex.exp_ofReal_mul_I_im]
            exact Real.sin_pos_of_pos_of_lt_pi hθpos hθpi
          simpa [g, norm_mul] using
            mul_le_mul (ha (u n) hus huim)
              (hb (-(u n)) (by simpa [mem_sphere] using hus) (by simpa using huim))
              (norm_nonneg _) (le_trans (norm_nonneg _) (ha (u n) hus huim)))
        simpa [g, norm_mul] using hend
      · let u : ℕ → ℂ := fun n ↦
          -Complex.exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
        have ht : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hc : Tendsto (fun n : ℕ ↦ ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
            atTop (nhds 0) := by
          simpa [Function.comp_def] using
            (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).mul
              (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ Complex.I) atTop (nhds Complex.I))
        have hu : Tendsto u atTop (nhds (-1)) := by
          simpa [u] using (Complex.continuous_exp.continuousAt.tendsto.comp hc).neg
        have hu_closed : ∀ n, u n ∈ closedBall (0 : ℂ) 1 := by
          intro n
          rw [mem_closedBall]
          simp [dist_zero_right, u, Complex.norm_exp]
        have hlim : Tendsto (fun n ↦ ‖g (u n)‖) atTop (nhds ‖g (-1)‖) :=
          ((hg_cont (-1) (by simp [mem_closedBall])).tendsto.comp
            (tendsto_nhdsWithin_iff.mpr
              ⟨hu, Filter.Eventually.of_forall hu_closed⟩)).norm
        have hend : ‖g (-1)‖ ≤ a * b := le_of_tendsto hlim (by
          filter_upwards with (n : ℕ)
          have hθpos : 0 < (1 / ((n : ℝ) + 1)) := one_div_pos.mpr (by positivity)
          have hθpi : (1 / ((n : ℝ) + 1)) < Real.pi :=
            lt_of_le_of_lt ((div_le_one (by positivity)).2 (by norm_num))
              (lt_trans (by norm_num) Real.pi_gt_three)
          have hus : u n ∈ sphere (0 : ℂ) 1 := by simp [u, Complex.norm_exp]
          have huim : (u n).im < 0 := by
            simp only [u]
            rw [neg_im, Complex.exp_ofReal_mul_I_im]
            exact neg_lt_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hθpos hθpi)
          simpa [g, norm_mul, mul_comm] using
            mul_le_mul
              (ha (-(u n)) (by simpa [mem_sphere] using hus) (by simpa using huim))
              (hb (u n) hus huim) (norm_nonneg _)
              (le_trans (norm_nonneg _)
                (ha (-(u n)) (by simpa [mem_sphere] using hus) (by simpa using huim))))
        simpa [g, norm_mul] using hend
    · exact mul_le_mul (ha z hzs hplus) (hb (-z) hnzs (by simpa using hplus))
        (norm_nonneg _) (le_trans (norm_nonneg _) (ha z hzs hplus))
  have hgzero : ‖g 0‖ ≤ a * b :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg_dc hfront
      (by simp [closure_ball])
  have hsquare : ‖f 0‖ ^ 2 ≤ a * b := by simpa [g, pow_two] using hgzero
  have ha0 : 0 ≤ a :=
    le_trans (norm_nonneg _) (ha Complex.I (by simp) (by simp))
  have hb0 : 0 ≤ b :=
    le_trans (norm_nonneg _) (hb (-Complex.I) (by simp) (by simp))
  exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg ha0 hb0)).2 hsquare

  -- Proof: g(z) = f(z)·f(-z). On the sphere, z↦-z swaps upper/lower arcs,
  -- so |g(z)| ≤ ab everywhere on the sphere. By max modulus, |g(0)| ≤ ab.
  -- Since g(0) = f(0)², |f(0)|² ≤ ab, so |f(0)| ≤ √(ab).
  --
  -- APIs needed:
  -- - `Complex.norm_le_of_forall_mem_frontier_norm_le` (max modulus principle)
  -- - `DiffContOnCl.mk_ball` from DifferentiableOn + ContinuousOn
  -- - `norm_mul`, `Real.le_sqrt`
