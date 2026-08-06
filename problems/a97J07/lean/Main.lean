/-
! # APM a97J07: Geometric-mean bound at the disk center via reflection + maximum modulus

f is continuous on closed disk {|z|≤1}, analytic on {|z|<1}.
|f(z)| ≤ a on upper semicircle, |f(z)| ≤ b on lower semicircle.
Prove |f(0)| ≤ √(ab).

## Strategy (from informal-solution.md)

Define g(z) = f(z)·f(-z). The reflection z ↦ -z swaps upper/lower semicircles,
so |g(z)| ≤ ab on the whole circle. By maximum modulus, |g(0)| ≤ ab.
Since g(0) = f(0)², we get |f(0)|² ≤ ab, hence |f(0)| ≤ √(ab).

## Phase-A hints dropped
All Phase-A hints were generic; none provided specific API guidance.
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.FDeriv.Mul

open Metric Set Filter Topology
open scoped Topology

noncomputable section

namespace APMa97J07

/-- Main theorem: ‖f(0)‖ ≤ √(ab) under the asymmetric boundary bounds.

    The proof uses the reflection trick: g(z) = f(z)·f(-z) satisfies ‖g‖ ≤ ab
    on the whole unit circle, so ‖g(0)‖ ≤ ab by the maximum modulus principle.
    Since g(0) = f(0)², this gives ‖f(0)‖² ≤ ab. -/
theorem geometric_mean_bound
    (f : ℂ → ℂ)
    (hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) 1))
    (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h_upper : ∀ z : ℂ, ‖z‖ = (1 : ℝ) → 0 ≤ (z.im) → ‖f z‖ ≤ a)
    (h_lower : ∀ z : ℂ, ‖z‖ = (1 : ℝ) → (z.im) ≤ 0 → ‖f z‖ ≤ b) :
    ‖f 0‖ ≤ Real.sqrt (a * b) := by
  -- Define g(z) = f(z) · f(-z)
  let g : ℂ → ℂ := fun z => f z * f (-z)

  -- g is DiffContOnCl on the open unit ball
  have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
    refine DifferentiableOn.mul hf_diff ?_
    have hneg : Differentiable ℂ (fun z : ℂ => -z) := differentiable_id.neg
    exact hf_diff.comp hneg.differentiableOn
      (fun z hz => by simpa using hz)
  have hg_cont : ContinuousOn g (Metric.closedBall (0 : ℂ) 1) := by
    refine (hf_cont.mul ?_)
    have : ContinuousOn (fun z : ℂ => f (-z)) (Metric.closedBall (0 : ℂ) 1) := by
      have hneg_cont : Continuous (fun z : ℂ => -z) := continuous_id.neg
      exact hf_cont.comp hneg_cont.continuousOn
        (fun z hz => by simpa [dist_zero_right, neg_neg] using hz)
    exact this
  have hg_dcc : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) 1) :=
    DiffContOnCl.mk_ball hg_diff hg_cont

  -- ‖g(z)‖ ≤ ab on the frontier (unit circle)
  have hg_bound : ∀ z ∈ frontier (Metric.ball (0 : ℂ) 1), ‖g z‖ ≤ a * b := by
    intro z hz
    have hz_sphere : z ∈ Metric.sphere (0 : ℂ) 1 :=
      frontier_ball_subset_sphere (α := ℂ) hz
    have hz_abs : ‖z‖ = (1 : ℝ) := by
      rw [Metric.sphere, mem_setOf, dist_zero_right] at hz_sphere
      exact hz_sphere
    rw [norm_mul]
    by_cases h : 0 ≤ z.im
    · -- z in upper arc, -z in lower arc
      have h1 : ‖f z‖ ≤ a := h_upper z hz_abs h
      have h2 : ‖f (-z)‖ ≤ b := by
        apply h_lower
        · simp [hz_abs]
        · show (-z).im ≤ 0
          simp
          linarith
      exact mul_le_mul h1 h2 (norm_nonneg _) ha
    · -- z in lower arc (z.im < 0), -z in upper arc
      push_neg at h
      have h1 : ‖f z‖ ≤ b := h_lower z hz_abs h.le
      have h2 : ‖f (-z)‖ ≤ a := by
        apply h_upper
        · simp [hz_abs]
        · show 0 ≤ (-z).im
          simp
          linarith
      exact (mul_le_mul h1 h2 (norm_nonneg _) hb).trans_eq (mul_comm b a)

  -- Maximum modulus principle: ‖g(0)‖ ≤ ab
  have hg0 : ‖g 0‖ ≤ a * b :=
    Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball (0 : ℂ) 1))
      hg_dcc hg_bound
      (subset_closure (by rw [Metric.mem_ball, dist_zero_right]; norm_num : (0 : ℂ) ∈ Metric.ball 0 1))

  -- g(0) = f(0)², so ‖f(0)‖² ≤ ab, hence ‖f(0)‖ ≤ √(ab)
  have hsq : ‖f 0‖ ^ 2 ≤ a * b := by
    have hg0' : ‖f 0 * f 0‖ ≤ a * b := by
      have : g 0 = f 0 * f 0 := by show f 0 * f (-(0:ℂ)) = f 0 * f 0; rw [neg_zero]
      rw [← this]; exact hg0
    rw [norm_mul] at hg0'
    nlinarith [sq_nonneg (‖f 0‖), norm_nonneg (f 0)]
  have h_ab_nn : 0 ≤ a * b := mul_nonneg ha hb
  have h_f0_nn : 0 ≤ ‖f 0‖ := norm_nonneg _
  -- ‖f(0)‖ ≤ √(ab) since ‖f(0)‖² ≤ ab and ‖f(0)‖ ≥ 0
  exact (Real.le_sqrt h_f0_nn (mul_nonneg ha hb)).mpr hsq

#print axioms APMa97J07.geometric_mean_bound

end APMa97J07
