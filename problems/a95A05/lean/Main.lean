/-
! # APM a95A05: Vanishing on a boundary arc implies identically zero

If f is analytic on the open unit disk, continuous on the closed disk, and
vanishes on the upper semicircle of the boundary, then f ≡ 0 on the disk.

## Proof strategy (from informal proof)

Define g(z) = f(z) · f(-z). Then:
- g is analytic on the disk (product of analytic functions).
- g is continuous on the closed disk.
- g vanishes on the entire boundary ∂Δ (not just the upper arc):
  - If Im(z) ≥ 0: f(z) = 0, so g(z) = 0.
  - If Im(z) < 0: then Im(-z) > 0 and |-z| = 1, so f(-z) = 0 and g(z) = 0.
- By the maximum modulus principle: g ≡ 0 on Δ.
- Since f(z)·f(-z) = 0 for all z ∈ Δ, either f ≡ 0 or f∘(-id) ≡ 0.
  But f∘(-id) ≡ 0 implies f ≡ 0 (substitute w = -z).

## Statement repair

The generated statements used `DifferentiableOn` and `ContinuousOn` separately.
We keep this but construct `DiffContOnCl` internally to apply the maximum
modulus principle (`eqOn_closure_of_eqOn_frontier`).
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.DiffContOnCl

open Complex Filter Metric Set
open scoped Topology

noncomputable section

/-- The auxiliary function g(z) = f(z) · f(-z). -/
def auxProd (f : ℂ → ℂ) (z : ℂ) : ℂ := f z * f (-z)

/-- g is differentiable on the open disk (product of analytic functions). -/
lemma auxProd_differentiableOn
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) :
    DifferentiableOn ℂ (auxProd f) (ball 0 1) := by
  have hneg : DifferentiableOn ℂ (fun z => f (-z)) (ball 0 1) := by
    have : Differentiable ℂ (Neg.neg : ℂ → ℂ) := differentiable_neg
    exact hf.comp this.differentiableOn (fun x hx => by
      simpa [norm_neg, mem_ball] using hx)
  exact DifferentiableOn.mul hf hneg

/-- g is continuous on the closed disk. -/
lemma auxProd_continuousOn
    {f : ℂ → ℂ} (hf : ContinuousOn f (closedBall 0 1)) :
    ContinuousOn (auxProd f) (closedBall 0 1) := by
  have hneg : ContinuousOn (fun z => f (-z)) (closedBall 0 1) := by
    have : Continuous (Neg.neg : ℂ → ℂ) := continuous_neg
    exact hf.comp this.continuousOn (fun x hx => by
      simpa [norm_neg, mem_closedBall] using hx)
  exact ContinuousOn.mul hf hneg

/-- g is DiffContOnCl on the disk. -/
lemma auxProd_diffContOnCl
    {f : ℂ → ℂ}
    (hf_diff : DifferentiableOn ℂ f (ball 0 1))
    (hf_cont : ContinuousOn f (closedBall 0 1)) :
    DiffContOnCl ℂ (auxProd f) (ball 0 1) := by
  refine ⟨auxProd_differentiableOn hf_diff, ?_⟩
  have : closure (ball 0 1 : Set ℂ) = closedBall 0 1 := by
    exact closure_ball 0 one_ne_zero
  rw [this]
  exact auxProd_continuousOn hf_cont

/-- g vanishes on the entire boundary ∂Δ.

For z on the unit circle:
- If Im z ≥ 0: f(z) = 0 by hypothesis.
- If Im z < 0: -z has Im(-z) > 0 and |-z| = 1, so f(-z) = 0. -/
lemma auxProd_vanish_on_frontier
    {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f (closedBall 0 1))
    (hf_vanish : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ z.im → f z = 0) :
    ∀ z ∈ frontier (ball 0 1 : Set ℂ), auxProd f z = 0 := by
  rw [frontier_ball 0 one_ne_zero]
  intro z hz
  by_cases him : 0 ≤ z.im
  · -- f(z) = 0 since z is on the sphere with Im z ≥ 0
    have h_fz := hf_vanish z hz him
    simp [auxProd, h_fz]
  · -- Im z < 0, so Im(-z) > 0 and |-z| = 1
    push_neg at him
    have h_neg_im : 0 ≤ (-z).im := by
      show 0 ≤ -(z.im)
      linarith
    have h_norm : ‖z‖ = 1 := by
      have : dist z 0 = 1 := hz
      rw [dist_zero_right] at this
      exact this
    have h_neg_sphere : -z ∈ sphere (0 : ℂ) 1 := by
      show dist (-z) 0 = 1
      rw [dist_zero_right, norm_neg, h_norm]
    have h_fneg := hf_vanish (-z) h_neg_sphere h_neg_im
    simp [auxProd, h_fneg]

/-- The ball (0 : ℂ) 1 is bounded. -/
lemma ball_bounded : Bornology.IsBounded (ball (0 : ℂ) 1) :=
  Metric.isBounded_ball

/-- Maximum modulus principle application: analytic on Δ, continuous on Δ̄,
zero on ∂Δ ⟹ zero on Δ̄.

Uses Mathlib's `Complex.eqOn_closure_of_eqOn_frontier`. -/
lemma eq_zero_on_closure_of_frontier_zero
    {g : ℂ → ℂ}
    (hg_diff : DifferentiableOn ℂ g (ball 0 1))
    (hg_cont : ContinuousOn g (closedBall 0 1))
    (hg_bdy : ∀ z ∈ frontier (ball 0 1 : Set ℂ), g z = 0) :
    ∀ z ∈ closedBall (0 : ℂ) 1, g z = 0 := by
  have hcl : closure (ball 0 1 : Set ℂ) = closedBall 0 1 :=
    closure_ball 0 one_ne_zero
  have hd : DiffContOnCl ℂ g (ball 0 1) := ⟨hg_diff, hcl ▸ hg_cont⟩
  have hzero : DiffContOnCl ℂ (0 : ℂ → ℂ) (ball 0 1) :=
    ⟨(differentiable_const (c := (0 : ℂ))).differentiableOn, continuousOn_const⟩
  have heg : EqOn g (fun _ => 0) (frontier (ball 0 1)) := by
    intro z hz
    exact hg_bdy z hz
  have h := Complex.eqOn_closure_of_eqOn_frontier ball_bounded hd hzero heg
  rwa [hcl] at h

/-- Main theorem: vanishing on the upper boundary arc forces f ≡ 0 on Δ.

The proof:
1. g = f(z)·f(-z) vanishes on all of ∂Δ (by auxProd_vanish_on_frontier).
2. Maximum modulus: g ≡ 0 on Δ̄.
3. f(z)·f(-z) = 0 for all z ∈ Δ, so f ≡ 0 (since Δ is connected). -/
theorem eq_zero_of_vanishing_on_upper_arc
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_cont : ContinuousOn f (closedBall 0 1))
    (hf_vanish : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ z.im → f z = 0) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
  have hprod_closed :
      ∀ z ∈ closedBall (0 : ℂ) 1, auxProd f z = 0 :=
    eq_zero_on_closure_of_frontier_zero
      (auxProd_differentiableOn hf_holo)
      (auxProd_continuousOn hf_cont)
      (auxProd_vanish_on_frontier hf_cont hf_vanish)
  have hprod : ∀ z ∈ ball (0 : ℂ) 1, auxProd f z = 0 :=
    fun z hz => hprod_closed z (ball_subset_closedBall hz)
  have hf_analytic : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1) :=
    hf_holo.analyticOnNhd isOpen_ball
  intro z hz
  by_contra hfz
  have hf_continuousAt : ContinuousAt f z :=
    (hf_holo z hz).differentiableAt (isOpen_ball.mem_nhds hz) |>.continuousAt
  have hneg_nonzero : ∀ᶠ w in 𝓝 (-z), f (-w) ≠ 0 := by
    have hcomp : ContinuousAt (fun w : ℂ => f (-w)) (-z) :=
      hf_continuousAt.comp_of_eq continuousAt_neg (by simp)
    exact hcomp.eventually_ne (by simpa using hfz)
  have hneg_mem : -z ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball, norm_neg] using hz
  have hball : ball (0 : ℂ) 1 ∈ 𝓝 (-z) :=
    isOpen_ball.mem_nhds hneg_mem
  have hf_eventually_zero : f =ᶠ[𝓝 (-z)] (fun _ => 0) := by
    filter_upwards [hneg_nonzero, hball] with w hn hw
    have hp : f w * f (-w) = 0 := by
      simpa [auxProd] using hprod w hw
    exact (mul_eq_zero.mp hp).resolve_right hn
  have hf_zero : EqOn f (fun _ => 0) (ball (0 : ℂ) 1) :=
    hf_analytic.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const (convex_ball 0 1).isPreconnected hneg_mem hf_eventually_zero
  exact hfz (hf_zero hz)

end
