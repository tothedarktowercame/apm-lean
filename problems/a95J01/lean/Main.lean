/-
! # APM a95J01: Subordination principle

If f, g are one-to-one analytic on Δ = {|z| < 1} with f(0) = g(0) and
f(Δ) ⊆ g(Δ), then |f'(0)| ≤ |g'(0)| with equality iff f = g ∘ (rotation).

## Proof strategy

1. Construct h = g⁻¹ ∘ f : Δ → Δ with h(0) = 0 (subordination function).
2. Schwarz lemma: |h'(0)| ≤ 1.
3. Chain rule: f'(0) = g'(0) · h'(0), so |f'(0)| ≤ |g'(0)|.
4. Equality: |h'(0)| = 1 → h is a rotation → f = g ∘ (rotation).

## Theory boundaries

- The Schwarz lemma (|h'(0)| ≤ 1) IS in Mathlib (`norm_deriv_le_one_of_mapsTo_ball`).
- The Schwarz equality case (|h'(0)| = 1 → rotation) is NOT in Mathlib.
- The existence of the analytic inverse g⁻¹ (needed for h = g⁻¹ ∘ f) requires
  the inverse function theorem for holomorphic functions, which is available
  in Mathlib but needs careful setup.

## Statement repair

The generated statements are structurally correct. We keep them as-is.
-/

import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

open Complex Metric Set Filter

noncomputable section

/-- The Schwarz lemma: h : Δ → Δ with h(0) = 0 satisfies ‖h'(0)‖ ≤ 1.

Directly from Mathlib's `norm_deriv_le_one_of_mapsTo_ball`. -/
lemma schwarz_deriv_bound
    {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh_maps : MapsTo h (ball 0 1) (ball 0 1))
    (hh_zero : h 0 = 0) :
    ‖deriv h 0‖ ≤ 1 := by
  have h01 : (0 : ℝ) < 1 := by norm_num
  have h_maps' : MapsTo h (ball 0 1) (closedBall (h 0) 1) := by
    intro z hz
    rw [hh_zero]
    exact ball_subset_closedBall (hh_maps hz)
  exact norm_deriv_le_one_of_mapsTo_ball hh h_maps' h01

/-- Chain rule: if f = g ∘ h on a neighborhood of 0, then f'(0) = g'(h(0)) · h'(0).

From Mathlib's `deriv.comp`. -/
lemma chain_rule_at_zero
    {f g h : ℂ → ℂ}
    (hg : DifferentiableAt ℂ g (h 0))
    (hh : DifferentiableAt ℂ h 0)
    (hfgh : ∀ᶠ z in nhds 0, f z = g (h z)) :
    deriv f 0 = deriv g (h 0) * deriv h 0 := by
  have hcomp :
      HasDerivAt (fun z => g (h z)) (deriv g (h 0) * deriv h 0) 0 :=
    hg.hasDerivAt.comp 0 hh.hasDerivAt
  exact (hcomp.congr_of_eventuallyEq hfgh).deriv

/-- The subordination argument after isolating the one missing construction lemma:
a holomorphic injection has nonvanishing derivative.  This formulation makes the
remaining formalization boundary explicit without importing the current
`ConstructionTargets.UnivalentDeriv`, whose corresponding theorem is not yet
axiom-clean. -/
lemma subordination_deriv_le_of_deriv_ne_zero
    {f g : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hg_holo : DifferentiableOn ℂ g (ball 0 1))
    (hg_inj : InjOn g (ball 0 1))
    (hfg_zero : f 0 = g 0)
    (hfg_sub : f '' ball 0 1 ⊆ g '' ball 0 1)
    (hg_deriv : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0) :
    ‖deriv f 0‖ ≤ ‖deriv g 0‖ := by
  classical
  let h : ℂ → ℂ := fun w ↦
    if hw : w ∈ g '' ball (0 : ℂ) 1 then Classical.choose hw else 0
  have h_mem {w : ℂ} (hw : w ∈ g '' ball (0 : ℂ) 1) :
      h w ∈ ball (0 : ℂ) 1 := by
    simp only [h, dif_pos hw]
    exact (Classical.choose_spec hw).1
  have gh {w : ℂ} (hw : w ∈ g '' ball (0 : ℂ) 1) : g (h w) = w := by
    simp only [h, dif_pos hw]
    exact (Classical.choose_spec hw).2
  have hg {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : h (g z) = z := by
    let hw : g z ∈ g '' ball (0 : ℂ) 1 := ⟨z, hz, rfl⟩
    exact hg_inj (h_mem hw) hz (gh hw)
  let k : ℂ → ℂ := fun z ↦ h (f z)
  have hk_maps : MapsTo k (ball (0 : ℂ) 1) (ball 0 1) := by
    intro z hz
    exact h_mem (hfg_sub ⟨z, hz, rfl⟩)
  have hk_zero : k 0 = 0 := by
    simpa [k, hfg_zero] using hg (mem_ball_self (by norm_num : (0 : ℝ) < 1))
  have hk_holo : DifferentiableOn ℂ k (ball 0 1) := by
    intro z hz
    have hfw : f z ∈ g '' ball (0 : ℂ) 1 := hfg_sub ⟨z, hz, rfl⟩
    have hx : h (f z) ∈ ball (0 : ℂ) 1 := h_mem hfw
    have hleft : ∀ᶠ y in nhds (h (f z)), h (g y) = y := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hg hy
    have hg_strict : HasStrictDerivAt g (deriv g (h (f z))) (h (f z)) :=
      (hg_holo.analyticAt (isOpen_ball.mem_nhds hx)).hasStrictDerivAt
    have hh_strict : HasStrictDerivAt h (deriv g (h (f z)))⁻¹ (f z) := by
      simpa only [gh hfw] using
        hg_strict.to_local_left_inverse (hg_deriv _ hx) hleft
    have hk_at := hh_strict.hasDerivAt.differentiableAt.comp z
      ((hf_holo z hz).differentiableAt (isOpen_ball.mem_nhds hz))
    simpa only [k, Function.comp_def] using hk_at.differentiableWithinAt
  have hk_bound : ‖deriv k 0‖ ≤ 1 := schwarz_deriv_bound hk_holo hk_maps hk_zero
  have hfactor : ∀ᶠ z in nhds 0, f z = g (k z) := by
    filter_upwards [isOpen_ball.mem_nhds
      (mem_ball_self (by norm_num : (0 : ℝ) < 1))] with z hz
    exact (gh (hfg_sub ⟨z, hz, rfl⟩)).symm
  have hk_at : DifferentiableAt ℂ k 0 :=
    (hk_holo 0 (mem_ball_self (by norm_num : (0 : ℝ) < 1))).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1)))
  have hg_at : DifferentiableAt ℂ g (k 0) := by
    rw [hk_zero]
    exact (hg_holo 0 (mem_ball_self (by norm_num : (0 : ℝ) < 1))).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1)))
  have hchain := chain_rule_at_zero hg_at hk_at hfactor
  rw [hk_zero] at hchain
  rw [hchain, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hk_bound

/-- Part (a): |f'(0)| ≤ |g'(0)| when f(Δ) ⊆ g(Δ) and f(0) = g(0).

The inverse construction, Schwarz bound, and chain rule are discharged above.
The sole remaining boundary is the local-degree theorem saying that a
holomorphic injection on an open set has nonvanishing derivative. -/
theorem subordination_deriv_le
    {f g : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hg_holo : DifferentiableOn ℂ g (ball 0 1))
    (hf_inj : InjOn f (ball 0 1))
    (hg_inj : InjOn g (ball 0 1))
    (hfg_zero : f 0 = g 0)
    (hfg_sub : f '' ball 0 1 ⊆ g '' ball 0 1) :
    ‖deriv f 0‖ ≤ ‖deriv g 0‖ := by
  apply subordination_deriv_le_of_deriv_ne_zero
    hf_holo hg_holo hg_inj hfg_zero hfg_sub
  intro z hz
  -- This is exactly the missing local-degree theorem.  The existing project
  -- construction target for it is not axiom-clean yet, so it cannot be used.
  sorry

/-- Part (b): Equality iff f(z) = g(e^{iα}z) for some α.

Inherits from (a) plus the Schwarz equality case (not in Mathlib). -/
theorem subordination_deriv_eq
    {f g : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hg_holo : DifferentiableOn ℂ g (ball 0 1))
    (hf_inj : InjOn f (ball 0 1))
    (hg_inj : InjOn g (ball 0 1))
    (hfg_zero : f 0 = g 0)
    (hfg_sub : f '' ball 0 1 ⊆ g '' ball 0 1)
    (heq : ‖deriv f 0‖ = ‖deriv g 0‖)
    (hg_ne : deriv g 0 ≠ 0) :
    ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1,
      f z = g (exp (I * ↑α) * z) := by
  sorry

/-- Schwarz equality: ‖h'(0)‖ = 1 ⟹ h(z) = e^{iα}z.

**Blocker:** Not in Mathlib. Mathlib has `norm_le_norm_of_mapsTo_ball`
(the inequality) but not the equality characterization. -/
lemma schwarz_equality
    {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh_maps : MapsTo h (ball 0 1) (ball 0 1))
    (hh_zero : h 0 = 0)
    (heq : ‖deriv h 0‖ = 1) :
    ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1, h z = exp (I * ↑α) * z := by
  sorry

end
