import Mathlib
import ApmCanaries.Frames.A93A03.Apm_v2_a93A03_1775002487121.Scratch

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace ApmCanaries.Frames.A93A03.Apm_v2_a93A03_1775002487121.Main

/-! # APM a93A03: Weak convergence in Hilbert spaces

  (a) Weak + norm convergence ⟹ strong convergence (Radon-Riesz).
  (b) Weak convergence ⟹ ‖h‖ ≤ lim inf ‖h_n‖.

  Pattern: norm_sub_sq_real gives ‖x-y‖² = ‖x‖² - 2⟨x,y⟩_ℝ + ‖y‖².
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Part (a): ‖h_n - h‖² = ‖h_n‖² - 2⟨h_n,h⟩ + ‖h‖² → 0. -/
theorem radon_riesz {h : H} {u : ℕ → H}
    (hweak : ∀ k : H, Tendsto (fun n => ⟪u n, k⟫_ℝ) atTop (𝓝 ⟪h, k⟫_ℝ))
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖h‖)) :
    Tendsto u atTop (𝓝 h) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- ‖u n - h‖² = ‖u n‖² - 2⟨u n, h⟩ + ‖h‖²
  have hkey : Tendsto (fun n => ‖u n - h‖ ^ 2) atTop (𝓝 0) := by
    have hexpand : ∀ n, ‖u n - h‖ ^ 2 = ‖u n‖ ^ 2 - 2 * ⟪u n, h⟫_ℝ + ‖h‖ ^ 2 :=
      fun n => @norm_sub_sq_real H _ _ (u n) h
    simp_rw [hexpand]
    have h1 : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 (‖h‖ ^ 2)) := hnorm.pow 2
    have h2 : Tendsto (fun n => 2 * ⟪u n, h⟫_ℝ) atTop (𝓝 (2 * ⟪h, h⟫_ℝ)) :=
      (hweak h).const_mul 2
    -- ⟨h,h⟩ = ‖h‖²: rewrite the limit target
    -- Remaining: combine h1, h2, const to get ‖h‖²-2‖h‖²+‖h‖²=0
    -- This needs real_inner_self_eq_norm_sq applied in the right context
    -- and Tendsto arithmetic to conclude. Blocked on type unification.
    sorry
  sorry

/-- Part (b): ‖h‖ ≤ lim inf ‖h_n‖.
  Proof sketch: ⟨u n, h⟩ ≤ ‖u n‖·‖h‖ by Cauchy-Schwarz. Taking limits:
  ‖h‖² = lim ⟨u n, h⟩ ≤ (lim inf ‖u n‖)·‖h‖. Divide by ‖h‖. -/
theorem weak_norm_le_liminf {h : H} {u : ℕ → H}
    (hweak : ∀ k : H, Tendsto (fun n => ⟪u n, k⟫_ℝ) atTop (𝓝 ⟪h, k⟫_ℝ)) :
    ‖h‖ ≤ liminf (fun n => (‖u n‖ : ℝ)) atTop := by
  -- Cauchy-Schwarz: ⟨u n, h⟩ ≤ ‖u n‖ · ‖h‖
  -- lim ⟨u n, h⟩ = ‖h‖² ≤ (lim inf ‖u n‖) · ‖h‖
  -- Divide by ‖h‖ (or handle ‖h‖ = 0 separately)
  sorry

end ApmCanaries.Frames.A93A03.Apm_v2_a93A03_1775002487121.Main
