import Mathlib

open Complex Filter Metric Set

noncomputable section

/-!
# APM a94A08

## Statement repairs

None.

## Encoding notes

The source numbers its iterates from `f₁ = f`; consequently the Lean sequence uses
`f^[n + 1]` rather than the zeroth iterate. Uniform convergence on
every compact subset is stated directly with `TendstoUniformlyOn`.
-/

theorem apm_a94a08
    {f : ℂ → ℂ}
    (hf_analytic : DifferentiableOn ℂ f (ball 0 1))
    (hf_selfmap : MapsTo f (ball 0 1) (ball 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ < 1) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 1 →
      TendstoUniformlyOn
        (fun n ↦ f^[n + 1])
        (fun _ : ℂ ↦ 0) atTop K := by
  -- Key tool: `dslope f 0 z` = f(z)/z for z≠0, = deriv f 0 for z=0.
  -- Identity: f z = z · dslope f 0 z (from `sub_smul_dslope`).
  -- -- (Pattern: math-formalization/complex-polynomial-bound — Schwarz lemma + max modulus)
  intro K hK hK_sub
  -- MapsTo f (ball 0 1) (closedBall (f 0) 1) for Schwarz lemma.
  have h_maps_closed : MapsTo f (ball 0 1) (closedBall (f 0 : ℂ) 1) := fun z hz => by
    rw [hf_zero]
    exact ball_subset_closedBall (hf_selfmap hz)
  -- ‖dslope f 0 z‖ ≤ 1 for z ∈ ball 0 1 (Schwarz lemma with R₁=R₂=1).
  have h_dslope_le : ∀ z ∈ ball (0 : ℂ) 1, ‖dslope f 0 z‖ ≤ 1 := by
    intro z hz
    have := norm_dslope_le_div_of_mapsTo_ball hf_analytic h_maps_closed hz
    simpa using this
  -- dslope f 0 is continuous on ball 0 1.
  have h_dslope_cont : ContinuousOn (dslope f 0) (ball (0 : ℂ) 1) := by
    rw [continuousOn_dslope (ball_mem_nhds _ (by norm_num : (0:ℝ) < 1))]
    exact ⟨hf_analytic.continuousOn,
      hf_analytic.differentiableAt (ball_mem_nhds _ (by norm_num : (0:ℝ) < 1))⟩
  -- ‖dslope f 0 z‖ < 1 strictly on ball 0 1.
  have h_dslope_strict : ∀ z ∈ ball (0 : ℂ) 1, ‖dslope f 0 z‖ < 1 := by
    intro z hz
    by_contra hne
    push_neg at hne
    have h_eq : ‖dslope f 0 z‖ = 1 := le_antisymm (h_dslope_le z hz) hne
    -- Equality case: f w = dslope f 0 z · w on ball 0 1
    have h_affine : EqOn f (fun w => f 0 + (w - 0) • dslope f 0 z) (ball 0 1) :=
      affine_of_mapsTo_ball_of_norm_dslope_eq_div
        hf_analytic h_maps_closed hz (by simp [h_eq])
    -- deriv f 0 = dslope f 0 z (since f w = w · dslope f 0 z near 0, as f 0 = 0)
    have h_deriv : deriv f 0 = dslope f 0 z := by
      have heq : f =ᶠ[nhds (0:ℂ)] fun w => w • dslope f 0 z := by
        filter_upwards [ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1)] with w hw
        have := h_affine hw
        simpa [hf_zero, sub_zero] using this
      rw [Filter.EventuallyEq.deriv_eq heq]
      have := (HasDerivAt.smul_const (hasDerivAt_id' (0:ℂ)) (dslope f 0 z)).deriv
      simpa using this
    rw [h_deriv] at hf_deriv
    linarith
  -- Embed K in ball 0 r for some r < 1 (compact subset of open ball).
  obtain ⟨r, hr_lt1, hKr_ball⟩ : ∃ r < (1 : ℝ), K ⊆ ball (0 : ℂ) r :=
    exists_lt_subset_ball hK.isClosed hK_sub
  -- Handle K = ∅ case directly.
  by_cases hK_empty : K = ∅
  · rw [tendstoUniformlyOn_iff]
    intro ε hε
    simp [hK_empty]
  -- r > 0 (since K nonempty ⊆ ball 0 r)
  have hr_pos : 0 < r := by
    by_contra hr
    push_neg at hr
    obtain ⟨z₀, hz₀⟩ := K.nonempty_iff_ne_empty.mpr hK_empty
    have hz₀_ball : z₀ ∈ ball (0:ℂ) r := hKr_ball hz₀
    have : ‖z₀‖ < 0 := lt_of_lt_of_le (mem_ball_zero_iff.mp hz₀_ball) hr
    exact absurd this (not_lt.mpr (norm_nonneg _))
  have hKr : K ⊆ closedBall (0 : ℂ) r := hKr_ball.trans ball_subset_closedBall
  -- closedBall 0 r is compact and contained in ball 0 1.
  have h_closedBall_compact : IsCompact (closedBall (0 : ℂ) r) :=
    isCompact_closedBall (0 : ℂ) r
  have h_closedBall_sub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) 1 :=
    closedBall_subset_ball hr_lt1
  -- ‖dslope f 0 ·‖ is continuous on closedBall 0 r.
  have h_norm_dslope_cont : ContinuousOn (fun z => ‖dslope f 0 z‖) (closedBall (0 : ℂ) r) := by
    have h_cont_sub : ContinuousOn (dslope f 0) (closedBall (0 : ℂ) r) :=
      h_dslope_cont.mono h_closedBall_sub
    exact fun z hz => (continuous_norm.continuousAt.comp_continuousWithinAt (h_cont_sub z hz))
  -- ‖dslope f 0 z‖ < 1 on closedBall 0 r.
  have h_strict_on_closedBall : ∀ z ∈ closedBall (0 : ℂ) r, ‖dslope f 0 z‖ < 1 :=
    fun z hz => h_dslope_strict z (h_closedBall_sub hz)
  -- Maximum of ‖dslope f 0 ·‖ on closedBall 0 r is lam < 1.
  obtain ⟨z₀, hz₀_mem, hz₀_max⟩ :=
    h_closedBall_compact.exists_isMaxOn
      (s := closedBall (0 : ℂ) r)
      ⟨0, mem_closedBall_self hr_pos.le⟩ h_norm_dslope_cont
  set lam := ‖dslope f 0 z₀‖
  have hlam_lt1 : lam < 1 := h_strict_on_closedBall z₀ hz₀_mem
  have hlam_nonneg : 0 ≤ lam := norm_nonneg _
  have hlam_bound : ∀ z ∈ closedBall (0 : ℂ) r, ‖dslope f 0 z‖ ≤ lam :=
    isMaxOn_iff.mp hz₀_max
  -- Contraction: ‖f z‖ = ‖z‖ · ‖dslope f 0 z‖ ≤ lam · ‖z‖
  have h_contr : ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ lam * ‖z‖ := by
    intro z hz
    have h_sub : z • dslope f 0 z = f z := by
      have : (z - 0) • dslope f 0 z = f z - f 0 := sub_smul_dslope f 0 z
      simpa [hf_zero, sub_zero] using this
    have hnorm : ‖f z‖ = ‖z‖ * ‖dslope f 0 z‖ := by
      rw [← h_sub, norm_smul]
    rw [hnorm, mul_comm]
    exact mul_le_mul_of_nonneg_right (hlam_bound z hz) (norm_nonneg (z : ℂ))
  -- f maps closedBall 0 r into itself.
  have h_selfmap_r : ∀ z ∈ closedBall (0 : ℂ) r, f z ∈ closedBall (0 : ℂ) r := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    calc ‖f z‖ ≤ lam * ‖z‖ := h_contr z hz
      _ ≤ lam * r := by gcongr; exact mem_closedBall_zero_iff.mp hz
      _ ≤ r := by nlinarith
  -- f^[n] maps closedBall 0 r to itself.
  have h_iter_mem : ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) r, f^[n] z ∈ closedBall (0 : ℂ) r := by
    intro n
    induction n with
    | zero => exact fun z hz => hz
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ']
      exact h_selfmap_r _ (ih z hz)
  -- Iterate: ‖f^[n] z‖ ≤ lam^n · ‖z‖ for z ∈ closedBall 0 r.
  have h_iter : ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) r, ‖f^[n] z‖ ≤ lam ^ n * ‖z‖ := by
    intro n
    induction n with
    | zero =>
      intro z _hz
      simp [pow_zero]
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ']
      have h_fz_in : f^[n] z ∈ closedBall (0 : ℂ) r := h_iter_mem n z hz
      calc ‖f (f^[n] z)‖ ≤ lam * ‖f^[n] z‖ := h_contr (f^[n] z) h_fz_in
        _ ≤ lam * (lam ^ n * ‖z‖) := by gcongr; exact ih z hz
        _ = lam ^ (n + 1) * ‖z‖ := by ring
  -- Prove uniform convergence using tendstoUniformlyOn_iff.
  rw [tendstoUniformlyOn_iff]
  intro ε hε
  have h_geom : Tendsto (fun n : ℕ => lam ^ (n + 1)) atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hlam_nonneg hlam_lt1
    exact this.comp (tendsto_add_atTop_nat 1)
  have hεr : 0 < ε / r := by positivity
  filter_upwards [h_geom.eventually (gt_mem_nhds hεr)] with n hn
  intro x hx
  rw [dist_zero_left]
  have hxr : x ∈ closedBall (0 : ℂ) r := hKr hx
  calc ‖f^[n+1] x‖ ≤ lam ^ (n+1) * ‖x‖ := h_iter (n+1) x hxr
    _ ≤ lam ^ (n+1) * r := by gcongr; exact mem_closedBall_zero_iff.mp hxr
    _ = r * lam ^ (n+1) := by rw [mul_comm]
    _ < r * (ε / r) := mul_lt_mul_of_pos_left hn hr_pos
    _ = ε := by rw [mul_div_cancel₀ ε hr_pos.ne']
