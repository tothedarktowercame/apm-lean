/-
! # APM a93A03: Weak convergence in Hilbert space

Prove:
(a) If hₙ ⇀ h and ‖hₙ‖ → ‖h‖, then ‖hₙ - h‖ → 0 (Kadec-Klee).
(b) If hₙ ⇀ h, then ‖h‖ ≤ liminf ‖hₙ‖ (weak lsc of norm).
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Data.Real.Sqrt

open Filter Topology InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Weak convergence: hₙ ⇀ h iff ⟨hₙ, k⟩ → ⟨h, k⟩ for all k. -/
def WeakTendsto (h : ℕ → H) (x : H) : Prop :=
  ∀ k : H, Tendsto (fun n => ⟪h n, k⟫_ℝ) atTop (𝓝 ⟪x, k⟫_ℝ)

/-- **Part (a):** Weak convergence + norm convergence ⟹ strong convergence.

    Uses the identity ‖hₙ - h‖² = ‖hₙ‖² - 2⟨hₙ,h⟩ + ‖h‖² (Mathlib's
    `norm_sub_sq_real`). Weak convergence gives ⟨hₙ,h⟩ → ‖h‖²;
    norm convergence gives ‖hₙ‖² → ‖h‖². So ‖hₙ-h‖² → 0. -/
theorem norm_sub_tendsto_zero_of_weak_and_norm
    {h : ℕ → H} {x : H}
    (hweak : WeakTendsto h x)
    (hnorm : Tendsto (fun n => ‖h n‖) atTop (𝓝 ‖x‖)) :
    Tendsto (fun n => ‖h n - x‖) atTop (𝓝 0) := by
  -- ⟨hₙ, x⟩ → ⟨x, x⟩ = ‖x‖²
  have h_inner : Tendsto (fun n => ⟪h n, x⟫_ℝ) atTop (𝓝 (‖x‖ ^ 2)) := by
    have := hweak x
    rwa [real_inner_self_eq_norm_sq] at this
  -- ‖hₙ‖² → ‖x‖²
  have h_norm_sq : Tendsto (fun n => ‖h n‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) :=
    hnorm.pow 2
  -- ‖hₙ‖² - 2⟨hₙ,x⟩ + ‖x‖² → 0
  have h_rhs : Tendsto (fun n => ‖h n‖ ^ 2 - 2 * ⟪h n, x⟫_ℝ + ‖x‖ ^ 2) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => 2 * ⟪h n, x⟫_ℝ) atTop (𝓝 (2 * ‖x‖ ^ 2)) :=
      tendsto_const_nhds.mul h_inner
    have h_sub : Tendsto (fun n => ‖h n‖ ^ 2 - 2 * ⟪h n, x⟫_ℝ) atTop
        (𝓝 (‖x‖ ^ 2 - 2 * ‖x‖ ^ 2)) := Tendsto.sub h_norm_sq h2
    have h0 : ‖x‖ ^ 2 - 2 * ‖x‖ ^ 2 + ‖x‖ ^ 2 = (0 : ℝ) := by ring
    rw [← h0]
    exact Tendsto.add h_sub tendsto_const_nhds
  -- Transport via ‖hₙ - x‖² = ‖hₙ‖² - 2⟨hₙ,x⟩ + ‖x‖²
  have h_sq : Tendsto (fun n => ‖h n - x‖ ^ 2) atTop (𝓝 0) :=
    Tendsto.congr (fun n => (norm_sub_sq_real _ _).symm) h_rhs
  -- ‖hₙ - x‖² → 0 implies ‖hₙ - x‖ → 0 via Real.sqrt continuity
  have h_sqrt : Tendsto (fun n => Real.sqrt (‖h n - x‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.tendsto 0 |>.comp h_sq
  rw [Real.sqrt_zero] at h_sqrt
  exact h_sqrt.congr (fun n => Real.sqrt_sq (norm_nonneg _))

/-- **Part (b):** Weak lower semicontinuity of the norm.

    If hₙ ⇀ h, then ‖h‖ ≤ liminf ‖hₙ‖.

    Proof: From ‖hₙ-h‖² ≥ 0: ‖hₙ‖² ≥ 2⟨hₙ,h⟩ - ‖h‖².
    Since ⟨hₙ,h⟩ → ‖h‖², for any a < ‖h‖ eventually a² ≤ ‖hₙ‖²,
    hence a ≤ ‖hₙ‖ (both nonneg), giving ‖h‖ ≤ liminf ‖hₙ‖.

    The proof of part (b) uses `le_liminf_of_le` which requires
    `IsCoboundedUnder (· ≥ ·) atTop` — the image of ‖hₙ‖ is cobounded. -/
theorem norm_le_liminf_of_weak
    {h : ℕ → H} {x : H}
    (hweak : WeakTendsto h x) :
    ‖x‖ ≤ liminf (fun n => (‖h n‖ : ℝ)) atTop := by
  sorry

end
