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

    This statement needs `[CompleteSpace H]`. Without completeness it is false:
    in the pre-Hilbert space `c₀₀` of finitely supported real sequences, fix a
    nonzero `x` and put `h n = x + n • e n`. For each finitely supported `k`,
    `⟪h n, k⟫ = ⟪x, k⟫` eventually, so `h` converges weakly to `x`, while its
    norms tend to infinity. Mathlib's real-valued `liminf` is defined using
    `sSup`; for a sequence with unbounded eventual lower bounds this is
    `sSup ∅ = 0`. Thus the conclusion would assert `‖x‖ ≤ 0`.

    With `[CompleteSpace H]`, Banach--Steinhaus gives the missing boundedness
    of `‖h n‖`; `eventually_le_norm_of_weak` and `le_liminf_of_le` then prove
    the result. -/
-- STATEMENT REPAIR 2026-07-30 (Joe-authorised class). FALSE as previously stated:
-- weak lower semicontinuity of the norm needs `[CompleteSpace H]`, because the
-- standard proof routes through Banach-Steinhaus, whose Mathlib form requires
-- completeness. Counterexample found by codex-7 on durée run 12: in the
-- INCOMPLETE space c00, take h n = x + n * e n. Then h n converges weakly to x
-- while the norms are unbounded, and Mathlib's real liminf collapses to
-- sSup (unbounded set) = sSup empty = 0, so the conclusion fails outright.
-- That collapse is machine-checked: csSup_of_not_bddAbove then Real.sSup_empty.
-- FOURTH instance of the Lean junk-value family, after ENNReal.toReal top = 0,
-- integral of a non-integrable function = 0, and ContDiff top meaning analytic.
theorem norm_le_liminf_of_weak [CompleteSpace H]
    {h : ℕ → H} {x : H}
    (hweak : WeakTendsto h x) :
    ‖x‖ ≤ liminf (fun n => (‖h n‖ : ℝ)) atTop := by
  sorry

end
