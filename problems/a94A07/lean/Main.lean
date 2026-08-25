import Mathlib

noncomputable section

open Filter Topology Metric

/-!
# APM a94A07

## Statement repairs
None.

## Encoding notes
An entire function is encoded by `Differentiable ℂ f`, and one-to-one by
`Function.Injective f`.

## Proof route
Avoid the blocked "f must be a polynomial" classification entirely. Build the
reciprocal difference quotient G, show it is entire with linear growth, apply
Liouville to its difference quotient Q, conclude G is a nonzero constant, and
unroll. Injectivity is used exactly twice: to make the local inverse global
(giving linear growth of G) and to keep `f z - f w` nonzero.
-/

theorem apm_a94a07
    {f : ℂ → ℂ}
    (hf_entire : Differentiable ℂ f)
    (hf_injective : Function.Injective f) :
    ∃ a₀ a₁ : ℂ, a₁ ≠ 0 ∧ ∀ z : ℂ, f z = a₀ + a₁ * z := by
  -- Step 1: a point with nonzero derivative.
  obtain ⟨w, hw⟩ : ∃ w, deriv f w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact absurd (hf_injective (is_const_of_deriv_eq_zero hf_entire hcon 0 1))
      (by norm_num : (0 : ℂ) ≠ 1)
  have hfwne : ∀ z, z ≠ w → f z - f w ≠ 0 := by
    intro z hz h
    exact hz (hf_injective (sub_eq_zero.mp h))
  -- Step 2: the local inverse, made global on a ball via injectivity.
  have hfs : HasStrictDerivAt f (deriv f w) w := (hf_entire.analyticAt w).hasStrictDerivAt
  set r := hfs.localInverse f (deriv f w) w hw with hr_def
  have hra : AnalyticAt ℂ r (f w) := (hf_entire.analyticAt w).analyticAt_localInverse hw
  have hrfw : r (f w) = w := hf_injective ((hfs.eventually_right_inverse hw).self_of_nhds)
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ z : ℂ, ‖f z - f w‖ < δ → r (f z) = z ∧ ‖z - w‖ < 1 := by
    obtain ⟨ε₁, hε₁0, hε₁⟩ := Metric.continuousAt_iff.mp hra.continuousAt 1 (by norm_num)
    obtain ⟨ε₂, hε₂0, hε₂⟩ :=
      Metric.eventually_nhds_iff.mp (hfs.eventually_right_inverse hw)
    refine ⟨min ε₁ ε₂, lt_min hε₁0 hε₂0, fun z hz => ?_⟩
    have hz1 : dist (f z) (f w) < ε₁ :=
      lt_of_lt_of_le (by simpa [dist_eq_norm] using hz) (min_le_left _ _)
    have hz2 : dist (f z) (f w) < ε₂ :=
      lt_of_lt_of_le (by simpa [dist_eq_norm] using hz) (min_le_right _ _)
    obtain ⟨h1, h2⟩ : f (r (f z)) = f z ∧ dist (r (f z)) (r (f w)) < 1 :=
      ⟨hε₂ hz2, hε₁ hz1⟩
    have h3 : r (f z) = z := hf_injective h1
    rw [h3, hrfw] at h2
    exact ⟨h3, by simpa [dist_eq_norm] using h2⟩
  have hfar : ∀ z : ℂ, ‖w‖ + 1 ≤ ‖z‖ → δ ≤ ‖f z - f w‖ := by
    intro z hz
    by_contra hlt
    obtain ⟨h1, h2⟩ := hδ z (lt_of_not_ge hlt)
    have h3 : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by simpa using norm_add_le (z - w) w
    linarith
  -- Step 3: the reciprocal difference quotient G.
  set G : ℂ → ℂ := fun z => if z = w then (deriv f w)⁻¹ else (z - w) / (f z - f w) with hG
  have hGw : G w = (deriv f w)⁻¹ := by simp [hG]
  have hGval : ∀ z, z ≠ w → G z = (z - w) / (f z - f w) := fun z hz => by simp [hG, hz]
  have hGdiff : ∀ z, z ≠ w → DifferentiableAt ℂ G z := by
    intro z hz
    have hd : DifferentiableAt ℂ (fun z => (z - w) / (f z - f w)) z :=
      (differentiableAt_id.sub (differentiableAt_const w)).div
        ((hf_entire z).sub (differentiableAt_const (f w))) (hfwne z hz)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hz] with x hx
    exact hGval x hx
  have hGeq : G =ᶠ[𝓝[≠] w] fun z => (slope f w z)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hGval x hx, div_eq_inv_mul]
    simp [slope]
  have hsl : Tendsto (fun z => (slope f w z)⁻¹) (𝓝[≠] w) (𝓝 (deriv f w)⁻¹) :=
    ((hasDerivAt_iff_tendsto_slope.mp (hf_entire w).hasDerivAt)).inv₀ hw
  have hcontG : ContinuousAt G w := by
    rw [continuousAt_iff_punctured_nhds, hGw]
    exact hsl.congr' hGeq.symm
  have hGentire : Differentiable ℂ G := by
    intro z
    rcases eq_or_ne z w with rfl | hz
    · exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        (by filter_upwards [self_mem_nhdsWithin] with x hx
            exact hGdiff x hx) hcontG).differentiableAt
    · exact hGdiff z hz
  have hGne : ∀ z, G z ≠ 0 := by
    intro z hz0
    rcases eq_or_ne z w with rfl | hzw
    · exact hw (inv_eq_zero.mp (hGw ▸ hz0))
    · rw [hGval z hzw] at hz0
      rcases div_eq_zero_iff.mp hz0 with h | h
      · exact hzw (sub_eq_zero.mp h)
      · exact hfwne z hzw h
  -- Linear growth of G.
  have hGfar : ∀ z : ℂ, ‖w‖ + 1 ≤ ‖z‖ → ‖G z‖ ≤ (‖z‖ + ‖w‖) / δ := by
    intro z hz
    have hzw : z ≠ w := by intro h; rw [h] at hz; have := norm_nonneg w; linarith
    have hdz : δ ≤ ‖f z - f w‖ := hfar z hz
    have hd0 : (0 : ℝ) < δ := hδ0
    have hnefw : (0 : ℝ) < ‖f z - f w‖ := lt_of_lt_of_le hd0 hdz
    rw [hGval z hzw, norm_div]
    have h1 : ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
    rw [div_le_div_iff₀ hnefw hd0]
    exact mul_le_mul h1 hdz hδ0.le (by positivity)
  obtain ⟨B, hB⟩ : ∃ B, ∀ z ∈ closedBall (0 : ℂ) (‖w‖ + 1), ‖G z‖ ≤ B := by
    obtain ⟨z₀, hmem, hmax⟩ := (isCompact_closedBall (0 : ℂ) (‖w‖ + 1)).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self (by positivity)⟩ (hGentire.continuous.continuousOn.norm)
    exact ⟨‖G z₀‖, fun z hz => hmax hz⟩
  set K : ℝ := max B ((1 + ‖w‖) / δ) with hK
  have hK0 : (0 : ℝ) ≤ K := le_max_iff.mpr (Or.inr (by positivity))
  have hGlin : ∀ z : ℂ, ‖G z‖ ≤ K * (1 + ‖z‖) := by
    intro z
    rcases le_or_gt (‖w‖ + 1) ‖z‖ with h | h
    · have h1 : ‖z‖ + ‖w‖ ≤ (1 + ‖z‖) * (1 + ‖w‖) := by
        nlinarith [norm_nonneg z, norm_nonneg w]
      have h2 : (‖z‖ + ‖w‖) / δ ≤ K * (1 + ‖z‖) := by
        have ha := div_le_div_of_nonneg_right h1 hδ0.le
        have hb : ((1 + ‖z‖) * (1 + ‖w‖)) / δ = (1 + ‖z‖) * ((1 + ‖w‖) / δ) := by field_simp
        have hc : (1 + ‖z‖) * ((1 + ‖w‖) / δ) ≤ K * (1 + ‖z‖) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        rw [hb] at ha
        exact le_trans ha hc
      exact le_trans (hGfar z h) h2
    · have hBz : z ∈ closedBall (0 : ℂ) (‖w‖ + 1) := by
        show dist z 0 ≤ ‖w‖ + 1
        rw [dist_zero_right]
        exact h.le
      have h4 : B ≤ K := le_max_left _ _
      have h5 : B * (1 + ‖z‖) ≤ K * (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_right h4 (by linarith [norm_nonneg z])
      have h6 : ‖G z‖ ≤ B * (1 + ‖z‖) := by
        have hB0 : (0 : ℝ) ≤ B :=
          le_trans (norm_nonneg (G 0)) (hB 0 (Metric.mem_closedBall_self (by positivity)))
        have := hB z hBz
        nlinarith [norm_nonneg z, hB0]
      exact le_trans h6 h5
  -- Step 4: Liouville on the difference quotient of G.
  set Q : ℂ → ℂ := fun z => if z = w then deriv G w else (G z - G w) / (z - w) with hQ
  have hQw : Q w = deriv G w := by simp [hQ]
  have hQval : ∀ z, z ≠ w → Q z = (G z - G w) / (z - w) := fun z hz => by simp [hQ, hz]
  have hQdiff : ∀ z, z ≠ w → DifferentiableAt ℂ Q z := by
    intro z hz
    have hd : DifferentiableAt ℂ (fun z => (G z - G w) / (z - w)) z :=
      (((hGentire z).sub (differentiableAt_const (G w))).div
        (differentiableAt_id.sub (differentiableAt_const w)) (sub_ne_zero.mpr hz))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hz] with x hx
    exact hQval x hx
  have hGeqQ : Q =ᶠ[𝓝[≠] w] slope G w := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hQval x hx]
    simp [slope, div_eq_inv_mul]
  have hslopeQ : Tendsto (slope G w) (𝓝[≠] w) (𝓝 (deriv G w)) :=
    hasDerivAt_iff_tendsto_slope.mp (hGentire w).hasDerivAt
  have hcontQ : ContinuousAt Q w := by
    rw [continuousAt_iff_punctured_nhds, hQw]
    exact hslopeQ.congr' hGeqQ.symm
  have hQentire : Differentiable ℂ Q := by
    intro z
    rcases eq_or_ne z w with rfl | hz
    · exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        (by filter_upwards [self_mem_nhdsWithin] with x hx
            exact hQdiff x hx) hcontQ).differentiableAt
    · exact hQdiff z hz
  have hQfar : ∀ z : ℂ, max (2 * ‖w‖) (‖w‖ + 1) ≤ ‖z‖ → ‖Q z‖ ≤ 4 * K + 2 * ‖G w‖ := by
    intro z hR
    rw [max_le_iff] at hR
    obtain ⟨hR1, hR2⟩ := hR
    have hzw : z ≠ w := by intro h; rw [h] at hR2; linarith
    have hz1 : (1 : ℝ) ≤ ‖z‖ := by have := norm_nonneg w; linarith
    have htri : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by simpa using norm_add_le (z - w) w
    have hden : ‖z‖ ≤ 2 * ‖z - w‖ := by nlinarith
    have hdenpos : (0 : ℝ) < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
    rw [hQval z hzw, norm_div, div_le_iff₀ hdenpos]
    have hnum : ‖G z - G w‖ ≤ K * (1 + ‖z‖) + ‖G w‖ := by
      have h1 := hGlin z
      have h2 := norm_sub_le (G z) (G w)
      linarith
    have hgw0 : (0 : ℝ) ≤ ‖G w‖ := norm_nonneg _
    have c1 : (4 * K + 2 * ‖G w‖) * (‖z‖ / 2) ≤ (4 * K + 2 * ‖G w‖) * ‖z - w‖ := by
      nlinarith
    have ceq : (4 * K + 2 * ‖G w‖) * (‖z‖ / 2) = (2 * K + ‖G w‖) * ‖z‖ := by ring
    have c3 : K * (1 + ‖z‖) + ‖G w‖ ≤ (2 * K + ‖G w‖) * ‖z‖ := by
      nlinarith [hK0, hgw0, hz1]
    linarith
  obtain ⟨BQ, hBQ⟩ :
      ∃ BQ, ∀ z ∈ closedBall (0 : ℂ) (max (2 * ‖w‖) (‖w‖ + 1)), ‖Q z‖ ≤ BQ := by
    obtain ⟨z₀, hmem, hmax⟩ :=
      (isCompact_closedBall (0 : ℂ) (max (2 * ‖w‖) (‖w‖ + 1))).exists_isMaxOn
        ⟨0, Metric.mem_closedBall_self (by positivity)⟩ (hQentire.continuous.continuousOn.norm)
    exact ⟨‖Q z₀‖, fun z hz => hmax hz⟩
  have hQbound : ∀ p : ℂ, ‖Q p‖ ≤ max BQ (4 * K + 2 * ‖G w‖) := by
    intro p
    rcases le_or_gt (max (2 * ‖w‖) (‖w‖ + 1)) ‖p‖ with h | h
    · exact le_trans (hQfar p h) (le_max_right _ _)
    · exact le_trans (hBQ p (by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact h.le)) (le_max_left _ _)
  have hQbounded : Bornology.IsBounded (Set.range Q) := by
    rw [Metric.isBounded_iff]
    refine ⟨2 * max BQ (4 * K + 2 * ‖G w‖), ?_⟩
    intro x hx y hy
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    have h1 := hQbound z
    have h2 := hQbound y
    rw [dist_eq_norm]
    have h3 : ‖Q z - Q y‖ ≤ ‖Q z‖ + ‖Q y‖ := norm_sub_le _ _
    linarith
  have hQconst : ∀ z, Q z = Q w := fun z =>
    hQentire.apply_eq_apply_of_bounded hQbounded z w
  have hGaff : ∀ z, G z = G w + Q w * (z - w) := by
    intro z
    rcases eq_or_ne z w with hz | hz
    · rw [hz]; simp
    · have h1 : G z - G w = Q z * (z - w) := by
        rw [hQval z hz]
        exact (div_mul_cancel₀ _ (sub_ne_zero.mpr hz)).symm
      rw [hQconst z] at h1
      linear_combination h1
  have hc0 : Q w = 0 := by
    by_contra hc
    have h2 := hGaff (w - G w / Q w)
    apply hGne (w - G w / Q w)
    rw [h2]
    field_simp
    ring
  have hGconst : ∀ z, G z = G w := by
    intro z
    rw [hGaff z, hc0]
    ring
  have hGw0 : G w ≠ 0 := by rw [hGw]; exact inv_ne_zero hw
  -- Step 5: unroll.
  have key : ∀ z : ℂ, f z - f w = (z - w) * (G w)⁻¹ := by
    intro z
    rcases eq_or_ne z w with hz | hz
    · rw [hz]; simp
    · have h1' : G w = (z - w) / (f z - f w) := by
        rw [← hGconst z]
        exact hGval z hz
      have h1 : G w * (f z - f w) = z - w := (eq_div_iff (hfwne z hz)).mp h1'
      have hd0 : G w ≠ 0 := hGw0
      rw [← div_eq_mul_inv, eq_div_iff hd0]
      exact mul_comm (G w) (f z - f w) ▸ h1
  refine ⟨f w - (G w)⁻¹ * w, (G w)⁻¹, inv_ne_zero hGw0, fun z => ?_⟩
  have hk := key z
  linear_combination hk
