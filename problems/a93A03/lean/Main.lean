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
  have h_inner : Tendsto (fun n => ⟪h n, x⟫_ℝ) atTop (𝓝 (‖x‖ ^ 2)) := by
    have := hweak x
    rwa [real_inner_self_eq_norm_sq] at this
  have h_norm_sq : Tendsto (fun n => ‖h n‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) :=
    hnorm.pow 2
  have h_rhs : Tendsto (fun n => ‖h n‖ ^ 2 - 2 * ⟪h n, x⟫_ℝ + ‖x‖ ^ 2) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => 2 * ⟪h n, x⟫_ℝ) atTop (𝓝 (2 * ‖x‖ ^ 2)) :=
      tendsto_const_nhds.mul h_inner
    have h_sub : Tendsto (fun n => ‖h n‖ ^ 2 - 2 * ⟪h n, x⟫_ℝ) atTop
        (𝓝 (‖x‖ ^ 2 - 2 * ‖x‖ ^ 2)) := Tendsto.sub h_norm_sq h2
    have h0 : ‖x‖ ^ 2 - 2 * ‖x‖ ^ 2 + ‖x‖ ^ 2 = (0 : ℝ) := by ring
    rw [← h0]
    exact Tendsto.add h_sub tendsto_const_nhds
  have h_sq : Tendsto (fun n => ‖h n - x‖ ^ 2) atTop (𝓝 0) :=
    Tendsto.congr (fun n => (norm_sub_sq_real _ _).symm) h_rhs
  have h_sqrt : Tendsto (fun n => Real.sqrt (‖h n - x‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    Real.continuous_sqrt.tendsto 0 |>.comp h_sq
  rw [Real.sqrt_zero] at h_sqrt
  exact h_sqrt.congr (fun n => Real.sqrt_sq (norm_nonneg _))

/-- Helper: for any a < ‖x‖, eventually a ≤ ‖h n‖.

    From ‖hₙ-x‖² ≥ 0: ‖h n‖² ≥ 2⟨hₙ,x⟩ - ‖x‖².
    Since ⟨hₙ,x⟩ → ‖x‖² and a < ‖x‖: eventually 2⟨hₙ,x⟩ - ‖x‖² > a²,
    so ‖h n‖² ≥ a², hence ‖h n‖ ≥ a (both nonneg). -/
private lemma eventually_le_norm_of_weak
    {h : ℕ → H} {x : H} (hweak : WeakTendsto h x) :
    ∀ a : ℝ, a < ‖x‖ → ∀ᶠ n in atTop, a ≤ ‖h n‖ := by
  have h_inner : Tendsto (fun n => ⟪h n, x⟫_ℝ) atTop (𝓝 (‖x‖ ^ 2)) := by
    have := hweak x
    rwa [real_inner_self_eq_norm_sq] at this
  intro a ha
  by_cases ha_neg : a < 0
  · exact Eventually.of_forall fun _ => le_trans ha_neg.le (norm_nonneg _)
  push_neg at ha_neg
  have ha_sq : a ^ 2 < ‖x‖ ^ 2 := sq_lt_sq' (by linarith [norm_nonneg x]) ha
  have h_thresh : (a ^ 2 + ‖x‖ ^ 2) / 2 < ‖x‖ ^ 2 := by linarith
  have h_inner_ev : ∀ᶠ n in atTop, (a ^ 2 + ‖x‖ ^ 2) / 2 < ⟪h n, x⟫_ℝ :=
    h_inner.eventually (Ioi_mem_nhds h_thresh)
  filter_upwards [h_inner_ev] with n hn
  have h_id : ‖h n - x‖ ^ 2 = ‖h n‖ ^ 2 - 2 * ⟪h n, x⟫_ℝ + ‖x‖ ^ 2 :=
    norm_sub_sq_real _ _
  have h_nn : 0 ≤ ‖h n - x‖ ^ 2 := pow_nonneg (norm_nonneg _) 2
  have h_sq : a ^ 2 ≤ ‖h n‖ ^ 2 := by linarith
  exact (sq_le_sq₀ ha_neg (norm_nonneg _)).mp h_sq

/-- **Part (b):** Weak lower semicontinuity of the norm.

    If hₙ ⇀ h, then ‖h‖ ≤ liminf ‖hₙ‖.

    Mathematical proof: for any a < ‖x‖, eventually a ≤ ‖h n‖
    (see `eventually_le_norm_of_weak`). This means every a < ‖x‖ is an
    eventual lower bound, so ‖x‖ ≤ liminf ‖h n‖.

    The Lean proof is blocked on the liminf API: `le_liminf_of_le` requires
    `IsCoboundedUnder (· ≥ ·)` which needs the sequence bounded above,
    and `liminf_eq` + `le_csSup` needs `BddAbove`. -/
theorem norm_le_liminf_of_weak
    {h : ℕ → H} {x : H}
    (hweak : WeakTendsto h x) :
    ‖x‖ ≤ liminf (fun n => (‖h n‖ : ℝ)) atTop := by
  have h_ev := eventually_le_norm_of_weak hweak
  -- For every a < ‖x‖, eventually a ≤ ‖h n‖. This means a ≤ liminf.
  -- Use le_of_forall_sub_lt to avoid liminf API: show for all ε > 0,
  -- ‖x‖ - ε ≤ liminf, hence ‖x‖ ≤ liminf.
  -- For each ε > 0: ‖x‖ - ε < ‖x‖, so eventually ‖x‖ - ε ≤ ‖h n‖.
  -- This means ‖x‖ - ε is an eventual lower bound, so ‖x‖ - ε ≤ liminf.
  -- The liminf_eq route is blocked by BddAbove. Let me try le_liminf_of_le.
  -- le_liminf_of_le needs IsCoboundedUnder (· ≥ ·) atTop (fun n => ‖h n‖).
  -- IsCoboundedUnder = IsCobounded (· ≥ ·) (map u atTop)
  -- = ∃ b, ∀ a, (∀ᶠ y in map u atTop, y ≥ a) → b ≥ a
  -- For ‖h n‖ ≥ 0: any a ≤ 0 satisfies eventually a ≤ ‖h n‖, so a is a lower bound.
  -- We need b ≥ all such a. b = 0 works for a ≤ 0.
  -- For a > 0 with eventually a ≤ ‖h n‖: from h_ev, a < ‖x‖ is sufficient.
  -- But the IsCobounded condition quantifies over ALL a, not just a < ‖x‖.
  -- For a > ‖x‖: is a an eventual lower bound? Not from h_ev.
  -- But a could be if ‖h n‖ is large. In that case b ≥ a for all such a.
  -- This is impossible if ‖h n‖ → ∞.
  -- So IsCoboundedUnder genuinely fails for unbounded sequences.
  -- BUT: le_liminf_of_le uses csSup, and for unbounded S, csSup returns 0.
  -- In that case, the result (a ≤ liminf) would be a ≤ 0, which fails for a > 0.
  -- The issue is fundamental to the ConditionallyCompleteLattice of ℝ.
  -- Workaround: prove the result in EReal or use a different formulation.
  by_contra hcontra
  push_neg at hcontra
  -- hcontra : liminf (fun n => ‖h n‖) atTop < ‖x‖
  -- Pick c with liminf < c < ‖x‖
  obtain ⟨c, hc_lt_x, hc_gt_liminf⟩ : ∃ c, c < ‖x‖ ∧ liminf (fun n => (‖h n‖ : ℝ)) atTop < c := by
    exact ⟨(liminf (fun n => (‖h n‖ : ℝ)) atTop + ‖x‖) / 2,
           by linarith, by linarith⟩
  -- c < ‖x‖ → eventually c ≤ ‖h n‖
  have hc_ev : ∀ᶠ n in atTop, c ≤ ‖h n‖ := h_ev c hc_lt_x
  -- c ≤ ‖h n‖ eventually → c ≤ liminf (by definition of liminf as sup of eventual lower bounds)
  -- Try le_liminf_of_le with isBoundedDefault
  have hc_le_liminf : c ≤ liminf (fun n => (‖h n‖ : ℝ)) atTop := by
    refine le_liminf_of_le ?_ hc_ev
    sorry
  linarith

end
