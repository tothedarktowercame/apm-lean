import Mathlib

/-!
# APM a99J07 — polynomial growth from the unit-disk sup norm

The unit-disk norm is the real supremum of the norms attained by `p` on the
actual closed unit disk.  The degree parameter `N` is explicitly pinned to
`p.natDegree`, and the conclusion is precisely the source's global growth
bound.

## Statement repairs

None.

## Encoding questions

None. Complex absolute values use the current norm notation.
-/

open Set

noncomputable section

def a99J07SupNormUnitDisk (p : Polynomial ℂ) : ℝ :=
  sSup {r : ℝ | ∃ z : ℂ, ‖z‖ ≤ 1 ∧ r = ‖p.eval z‖}

/-- Compactness of the disk supplies the boundedness needed for `le_csSup`. -/
lemma apm_a99J07_supNorm_bddAbove (p : Polynomial ℂ) :
    BddAbove {r : ℝ | ∃ z : ℂ, ‖z‖ ≤ 1 ∧ r = ‖p.eval z‖} := by
  let K : Set ℂ := Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall 0 1
  have hc : Continuous fun z : ℂ => ‖p.eval z‖ := p.continuous.norm
  have hb : BddAbove ((fun z : ℂ => ‖p.eval z‖) '' K) :=
    (hK.image hc).bddAbove
  apply hb.mono
  rintro r ⟨z, hz, rfl⟩
  exact ⟨z, by simpa [K, Metric.mem_closedBall, dist_zero_right] using hz, rfl⟩

lemma apm_a99J07_eval_le_supNorm (p : Polynomial ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖p.eval z‖ ≤ a99J07SupNormUnitDisk p := by
  exact le_csSup (apm_a99J07_supNorm_bddAbove p) ⟨z, hz, rfl⟩

/-- Maximum modulus on the disk, derived from Mathlib's
`Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn`. -/
lemma apm_a99J07_poly_le_boundary (q : Polynomial ℂ) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ∃ v : ℂ, ‖v‖ = 1 ∧ ‖q.eval u‖ ≤ ‖q.eval v‖ := by
  have hne : (Metric.closedBall (0 : ℂ) 1).Nonempty :=
    Metric.nonempty_closedBall.mpr zero_le_one
  obtain ⟨x, hx, hxmax⟩ := isCompact_closedBall (0 : ℂ) 1 |>.exists_isMaxOn
    hne q.continuous.norm.continuousOn
  by_cases hxeq : ‖x‖ = 1
  · exact ⟨x, hxeq, hxmax (by
      simpa [Metric.mem_closedBall, dist_zero_right] using hu)⟩
  · have hxlt : ‖x‖ < 1 := lt_of_le_of_ne
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hx) hxeq
    have hxball : x ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right]
    have hxmax' : IsMaxOn (norm ∘ fun z => q.eval z) (Metric.ball (0 : ℂ) 1) x :=
      fun z hz => hxmax (Metric.ball_subset_closedBall hz)
    have heq := Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn
      (convex_ball (0 : ℂ) 1).isPreconnected Metric.isOpen_ball
      q.differentiable.diffContOnCl hxball hxmax'
    refine ⟨1, by simp, (hxmax (by
      simpa [Metric.mem_closedBall, dist_zero_right] using hu)).trans_eq ?_⟩
    have h1cl : (1 : ℂ) ∈ closure (Metric.ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
      simp
    simpa using (heq h1cl).symm

/-- On the unit circle, Mathlib's `Polynomial.eval₂_reflect_mul_pow`
identifies the reflected polynomial with the original one at the inverse. -/
lemma apm_a99J07_reflect_boundary (p : Polynomial ℂ) (N : ℕ)
    (hd : p.natDegree ≤ N) {v : ℂ} (hv : ‖v‖ = 1) :
    ‖(p.reflect N).eval v‖ ≤ a99J07SupNormUnitDisk p := by
  have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
  letI : Invertible v := invertibleOfNonzero hv0
  have hinv_norm : ‖⅟v‖ = 1 := by
    rw [invOf_eq_inv, norm_inv, hv, inv_one]
  have hpbound := apm_a99J07_eval_le_supNorm p hinv_norm.le
  have heval : (p.reflect N).eval v * (⅟v) ^ N = p.eval (⅟v) := by
    have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) (⅟v) N p hd
    simpa using h
  rw [← heval, norm_mul, norm_pow, hinv_norm, one_pow, mul_one] at hpbound
  exact hpbound

theorem apm_a99j07
    (p : Polynomial ℂ) (N : ℕ)
    (hN : 1 ≤ N) (hdegree : p.natDegree = N) :
    ∀ w : ℂ,
      ‖p.eval w‖ ≤
        a99J07SupNormUnitDisk p * (max (1 : ℝ) ‖w‖) ^ N := by
  intro w
  by_cases hw : ‖w‖ ≤ 1
  · simpa [max_eq_left hw] using apm_a99J07_eval_le_supNorm p hw
  · have hwlt : 1 < ‖w‖ := lt_of_not_ge hw
    have hw0 : w ≠ 0 := by
      intro he
      subst w
      norm_num at hwlt
    letI : Invertible w := invertibleOfNonzero hw0
    have hu : ‖⅟w‖ ≤ 1 := by
      rw [invOf_eq_inv, norm_inv]
      exact (inv_le_one₀ (norm_pos_iff.mpr hw0)).2 (le_of_lt hwlt)
    obtain ⟨v, hv, huv⟩ := apm_a99J07_poly_le_boundary (p.reflect N) hu
    have hvb := apm_a99J07_reflect_boundary p N hdegree.le hv
    have hqu : ‖(p.reflect N).eval (⅟w)‖ ≤ a99J07SupNormUnitDisk p := huv.trans hvb
    have hid := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) w N p hdegree.le
    have heq : (p.reflect N).eval (⅟w) * w ^ N = p.eval w := by simpa using hid
    rw [← heq, norm_mul, norm_pow, max_eq_right (le_of_lt hwlt)]
    exact mul_le_mul_of_nonneg_right hqu (pow_nonneg (norm_nonneg w) N)
