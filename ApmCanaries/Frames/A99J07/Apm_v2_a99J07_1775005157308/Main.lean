import Mathlib
import ApmCanaries.Frames.A99J07.Apm_v2_a99J07_1775005157308.Scratch

noncomputable section

open scoped Real Topology

open Complex Polynomial Metric Set

namespace ApmCanaries.Frames.A99J07.Apm_v2_a99J07_1775005157308.Main

/-- Sup norm of `p` on the closed unit disk. -/
noncomputable def supNormUnitDisk (p : Polynomial ℂ) : ℝ :=
  ⨆ z : Metric.closedBall (0 : ℂ) (1 : ℝ), ‖p.eval z‖

lemma norm_eval_le_supNormUnitDisk (p : Polynomial ℂ) {z : ℂ}
    (hz : ‖z‖ ≤ (1 : ℝ)) : ‖p.eval z‖ ≤ supNormUnitDisk p := by
  classical
  have hz' : z ∈ Metric.closedBall (0 : ℂ) (1 : ℝ) := by simpa using hz
  refine le_iSup_of_le ⟨z, hz'⟩ ?_
  simp [supNormUnitDisk]

lemma reverse_eval (p : Polynomial ℂ) {z : ℂ} (hz : z ≠ 0) :
    p.reverse.eval z = z ^ p.natDegree * p.eval z⁻¹ := by
  classical
  have hz' : z⁻¹ ≠ 0 := inv_ne_zero hz
  haveI : Invertible (z⁻¹) := invertibleOfNonzero hz'
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (z⁻¹) p
  simp [Polynomial.eval, inv_pow, inv_inv] at h
  have := congrArg (fun t : ℂ => t * z ^ p.natDegree) h
  have hzpow : z ^ p.natDegree ≠ 0 := pow_ne_zero _ hz
  have h1 : (z⁻¹) ^ p.natDegree * z ^ p.natDegree = 1 := by
    simpa [inv_pow, mul_comm, mul_left_comm, mul_assoc] using
      mul_inv_cancel hzpow
  simpa [mul_comm, mul_left_comm, mul_assoc, h1]
    using congrArg (fun t : ℂ => t * z ^ p.natDegree) h

lemma reverse_norm_le_on_sphere (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) 1) : ‖p.reverse.eval z‖ ≤ supNormUnitDisk p := by
  classical
  have hz_norm : ‖z‖ = 1 := by
    simpa [Metric.sphere, dist_eq, Complex.norm_eq_abs] using hz
  have hz_ne : z ≠ 0 := by
    simpa [hz_norm] using (show (‖z‖ ≠ 0) from by simpa [hz_norm] using one_ne_zero)
  have hzinv_norm : ‖z⁻¹‖ = 1 := by simpa [hz_norm] using norm_inv z
  have bound := norm_eval_le_supNormUnitDisk p (le_of_eq hzinv_norm)
  have hrev := reverse_eval p hz_ne
  have hpow : ‖z ^ p.natDegree‖ = 1 := by simpa [hz_norm] using congrArg _ (norm_pow z _)
  have : ‖p.reverse.eval z‖ = ‖p.eval z⁻¹‖ := by
    simpa [hrev, hpow]
  simpa [this] using bound

lemma reverse_bound_on_disk (p : Polynomial ℂ) {z : ℂ}
    (hz : ‖z‖ ≤ (1 : ℝ)) : ‖p.reverse.eval z‖ ≤ supNormUnitDisk p := by
  classical
  have hball : DiffContOnCl ℂ (fun z : ℂ => p.reverse.eval z) (Metric.ball (0 : ℂ) 1) :=
    (p.reverse.differentiable).diffContOnCl _
  refine
    norm_le_of_forall_mem_frontier_norm_le (isBounded_ball _ _) hball ?_ (by
      simpa using hz)
  intro z hz'
  have : z ∈ Metric.sphere (0 : ℂ) 1 := by simpa [Metric.frontier_ball] using hz'
  exact reverse_norm_le_on_sphere p this

lemma eval_bound_outside (p : Polynomial ℂ) {w : ℂ}
    (hw : 1 < ‖w‖) : ‖p.eval w‖ ≤ supNormUnitDisk p * ‖w‖ ^ p.natDegree := by
  classical
  have hw_ne : w ≠ 0 := by exact ne_of_gt (lt_of_lt_of_le zero_lt_one hw)
  have hzinv_le : ‖w⁻¹‖ ≤ (1 : ℝ) := by
    have := inv_le_one (show ‖w‖ ≠ 0 from by simpa using norm_ne_zero_iff.2 hw_ne)
    simpa [norm_inv] using this
  have hbound := reverse_bound_on_disk p hzinv_le
  have hrev := reverse_eval p (inv_ne_zero hw_ne)
  have : p.eval w = w ^ p.natDegree * p.reverse.eval (w⁻¹) := by
    -- apply lemma with `z = w⁻¹`
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (reverse_eval p (inv_ne_zero hw_ne)).symm
  have hnonnneg : 0 ≤ ‖w‖ ^ p.natDegree := pow_nonneg (norm_nonneg _) _
  have := mul_le_mul_of_nonneg_left hbound hnonnneg
  simpa [this, norm_pow, norm_inv, this] using this

/-- The desired sup-norm bound. -/
theorem polynomial_supNorm_bound (p : Polynomial ℂ) (w : ℂ) :
    ‖p.eval w‖ ≤ supNormUnitDisk p * (max (1 : ℝ) ‖w‖) ^ p.natDegree := by
  classical
  by_cases h : ‖w‖ ≤ (1 : ℝ)
  · have hmax : max (1 : ℝ) ‖w‖ = 1 := max_eq_left h
    have := norm_eval_le_supNormUnitDisk p h
    simpa [hmax, pow_zero, mul_one] using this
  · have hgt : 1 < ‖w‖ := lt_of_le_of_ne (le_of_not_gt h) (by simpa using h)
    have := eval_bound_outside p hgt
    have hmax : max (1 : ℝ) ‖w‖ = ‖w‖ := max_eq_right_of_lt hgt
    simpa [hmax] using this

end ApmCanaries.Frames.A99J07.Apm_v2_a99J07_1775005157308.Main
