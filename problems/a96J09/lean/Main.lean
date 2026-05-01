import Mathlib

open Complex Filter Topology Set Metric
open scoped Real

noncomputable section

/-- If an analytic function is defined on an open set containing the closed unit disk,
then the normalized derivatives `‖f⁽ⁿ⁾(0)‖ / n!` tend to `0`. -/
theorem apm_a96J09_coeff_tendsto_zero_of_contains_closed_disk
    (D : Set ℂ) (hD_open : IsOpen D)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f D)
    (hclosed : Metric.closedBall (0 : ℂ) 1 ⊆ D) :
    Tendsto (fun n : ℕ => ‖iteratedDeriv n f 0‖ / n.factorial) atTop (𝓝 0) := by
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_closedBall (0 : ℂ) (1 : ℝ)).exists_cthickening_subset_open hD_open hclosed
  have hbigClosed : Metric.closedBall (0 : ℂ) (1 + δ) ⊆ D := by
    intro z hz
    have hz' : z ∈ Metric.cthickening δ (Metric.closedBall (0 : ℂ) 1) := by
      rw [cthickening_closedBall hδpos.le (by positivity : (0 : ℝ) ≤ 1) (0 : ℂ)]
      simpa [add_comm] using hz
    exact hδsub hz'
  have hRpos : 0 < 1 + δ := by linarith
  have hdiff : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) (1 + δ)) :=
    hf.differentiableOn.diffContOnCl_ball hbigClosed
  have hcont : ContinuousOn f (Metric.sphere (0 : ℂ) (1 + δ)) :=
    (hdiff.continuousOn_ball).mono Metric.sphere_subset_closedBall
  have hbounded : Bornology.IsBounded (f '' Metric.sphere (0 : ℂ) (1 + δ)) :=
    (isCompact_sphere (0 : ℂ) (1 + δ)).image_of_continuousOn hcont |>.isBounded
  rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C, hCball⟩
  have hC : ∀ z ∈ Metric.sphere (0 : ℂ) (1 + δ), ‖f z‖ ≤ C := by
    intro z hz
    exact hCball (f z) ⟨z, hz, rfl⟩
  have hderiv_bound (n : ℕ) :
      ‖iteratedDeriv n f 0‖ ≤ n.factorial * C / (1 + δ) ^ n := by
    simpa using
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
        (f := f) (c := (0 : ℂ)) (R := 1 + δ) (C := C) n hRpos hdiff hC
  have hseq_bound (n : ℕ) :
      ‖iteratedDeriv n f 0‖ / n.factorial ≤ C / (1 + δ) ^ n := by
    have hfact_pos : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    refine (div_le_iff₀ hfact_pos).2 ?_
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hderiv_bound n
  have hone_lt_R : 1 < 1 + δ := by linarith
  have hratio : |(1 / (1 + δ : ℝ))| < 1 := by
    rw [abs_of_pos (one_div_pos.mpr hRpos)]
    rw [div_lt_one hRpos]
    linarith
  have hpow : Tendsto (fun n : ℕ => (1 / (1 + δ : ℝ)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio
  have hgeom : Tendsto (fun n : ℕ => C / (1 + δ) ^ n) atTop (𝓝 0) := by
    have hpow' : Tendsto (fun n : ℕ => C * ((1 + δ : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
      simpa [one_div_pow] using (tendsto_const_nhds.mul hpow)
    simpa [div_eq_mul_inv] using hpow'
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity)
    (Eventually.of_forall hseq_bound) hgeom

/-- Main theorem for APM a96J09. -/
theorem apm_a96J09_main
    (D : Set ℂ) (hD_open : IsOpen D) (_hD_zero : (0 : ℂ) ∈ D)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f D)
    (hlimsup : 0 < limsup (fun n : ℕ => ‖iteratedDeriv n f 0‖ / n.factorial) atTop) :
    ¬ Metric.closedBall (0 : ℂ) 1 ⊆ D := by
  intro hclosed
  have hzero :
      limsup (fun n : ℕ => ‖iteratedDeriv n f 0‖ / n.factorial) atTop = 0 :=
    (apm_a96J09_coeff_tendsto_zero_of_contains_closed_disk D hD_open f hf hclosed).limsup_eq
  have : ¬ 0 < limsup (fun n : ℕ => ‖iteratedDeriv n f 0‖ / n.factorial) atTop := by
    simp [hzero]
  exact this hlimsup
