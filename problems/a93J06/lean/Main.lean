import Mathlib
import ApmCanaries.Frames.A93J06.Apm_v2_a93J06_1775002790071.Scratch

noncomputable section

open Complex Filter Metric Set
open scoped Real Topology

namespace ApmCanaries.Frames.A93J06.Apm_v2_a93J06_1775002790071.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

/-- Schwarz lemma applied to `f'` under the hypotheses of the problem. -/
theorem deriv_norm_le_norm
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hf'0 : deriv f 0 = 0)
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖deriv f z‖ ≤ 1) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖deriv f z‖ ≤ ‖z‖ := by
  intro z hz
  exact norm_le_norm_of_mapsTo_ball (hf.deriv isOpen_ball)
    (by
      intro w hw
      simpa [mem_closedBall_zero_iff] using hbound w hw)
    hf'0 (by simpa [mem_ball_zero_iff] using hz)

/-- If `f(0) = f'(0) = 0` and `|f'| ≤ 1` on the unit disk, then `|f(z)| ≤ |z|² / 2`. -/
theorem schwarz_second_order_bound
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hf0 : f 0 = 0)
    (hf'0 : deriv f 0 = 0)
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖deriv f z‖ ≤ 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ‖f z‖ ≤ ‖z‖ ^ 2 / 2 := by
  have hz_norm : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  let g : ℝ → ℂ := fun t => f ((t : ℂ) * z)
  have htz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (t : ℂ) * z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)).trans_lt (by simpa using hz_norm)
  have hgderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt g (deriv f ((t : ℂ) * z) * z) t := by
    have hout := (hf.differentiableAt (isOpen_ball.mem_nhds (htz t ht))).hasDerivAt
    have hin : HasDerivAt (fun w : ℂ => w * z) z (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const z
    simpa [g] using (hout.comp (t : ℂ) hin).comp_ofReal
  have hgcont : ContinuousOn g (Icc (0 : ℝ) 1) :=
    fun t ht => (hgderiv t ht).continuousAt.continuousWithinAt
  have hgdiff : DifferentiableOn ℝ g (Ioo (0 : ℝ) 1) :=
    fun t ht => (hgderiv t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
  have hderiv_bound :
      ∀ᵐ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
        ‖deriv g t‖ ≤ t * ‖z‖ ^ 2 := by
    filter_upwards [] with t ht
    rw [(hgderiv t ⟨ht.1.le, ht.2.le⟩).deriv, norm_mul]
    have hschwarz :=
      deriv_norm_le_norm hf hf'0 hbound ((t : ℂ) * z)
        (htz t ⟨ht.1.le, ht.2.le⟩)
    calc
      ‖deriv f ((t : ℂ) * z)‖ * ‖z‖ ≤ ‖(t : ℂ) * z‖ * ‖z‖ := by
        gcongr
      _ = t * ‖z‖ ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
        ring
  have hmain :=
    norm_sub_le_integral_of_norm_deriv_le_of_le (f := g) (B := fun t => t * ‖z‖ ^ 2)
      (show (0 : ℝ) ≤ 1 by norm_num) hgcont hgdiff hderiv_bound
      ((continuous_id.mul
        (continuous_const : Continuous (fun _ : ℝ => ‖z‖ ^ 2))).intervalIntegrable 0 1)
  rw [show g 1 = f z by simp [g], show g 0 = f 0 by simp [g], hf0, sub_zero] at hmain
  calc
    ‖f z‖ ≤ ∫ t : ℝ in (0 : ℝ)..1, t * ‖z‖ ^ 2 := hmain
    _ = ‖z‖ ^ 2 / 2 := by
      rw [intervalIntegral.integral_mul_const, integral_id]
      ring

end ApmCanaries.Frames.A93J06.Apm_v2_a93J06_1775002790071.Main
