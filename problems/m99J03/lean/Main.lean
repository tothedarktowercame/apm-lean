import Mathlib

/-!
# APM m99J03

## Statement repairs

In part (a), the second condition `x ≤ 1/n` is repaired to `|x| ≤ 1/n`.
As printed, it overlaps the first condition whenever `x < -1/n`; the symmetric
absolute-value condition is the unique reading consistent with the stated piecewise
function and the supplied solution.

## Encoding questions

Convergence in `𝒟'(ℝ)` is encoded by its defining weak condition: convergence of
the associated integral against every smooth compactly supported test function.
-/

noncomputable section

def apm_m99j03_IsTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

def apm_m99j03_triangle (n : ℕ) (x : ℝ) : ℝ :=
  if |x| > 1 / (n : ℝ) then 0
  else (n : ℝ) * (1 - (n : ℝ) * |x|)

def apm_m99j03_dipole (n : ℕ) (x : ℝ) : ℝ :=
  if -(1 / (n : ℝ)) < x ∧ x < 0 then (n : ℝ) ^ 2
  else if 0 ≤ x ∧ x ≤ 1 / (n : ℝ) then -((n : ℝ) ^ 2)
  else 0

/-- The triangular kernel is the unit profile transported by the dilation
`x ↦ n*x`, including its normalizing Jacobian factor. -/
lemma apm_m99j03_triangle_eq_scaled_profile {n : ℕ} (hn : 0 < n) (x : ℝ) :
    apm_m99j03_triangle n x =
      (n : ℝ) * apm_m99j03_triangle 1 ((n : ℝ) * x) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have habs : |(n : ℝ) * x| = (n : ℝ) * |x| := by
    rw [abs_mul, abs_of_pos hnR]
  have hscale : |(n : ℝ) * x| > 1 ↔ |x| > 1 / (n : ℝ) := by
    have hinv : (1 / (n : ℝ)) * n = 1 := by field_simp
    constructor
    · intro h
      rw [habs] at h
      nlinarith
    · intro h
      rw [habs]
      nlinarith
  unfold apm_m99j03_triangle
  simp only [Nat.cast_one, one_div_one]
  by_cases hx : |x| > 1 / (n : ℝ)
  · have hnx := hscale.mpr hx
    rw [if_pos hx, if_pos hnx]
    simp
  · have hnx : ¬|(n : ℝ) * x| > 1 := not_congr hscale |>.mpr hx
    rw [if_neg hx, if_neg hnx]
    simp [habs]

/-- A continuous max-form for the unit triangular profile. -/
lemma apm_m99j03_triangle_one_eq_max (x : ℝ) :
    apm_m99j03_triangle 1 x = max (1 - |x|) 0 := by
  unfold apm_m99j03_triangle
  simp only [Nat.cast_one, one_div_one, one_mul]
  by_cases hx : |x| > 1
  · rw [if_pos hx, max_eq_right]
    linarith
  · rw [if_neg hx, max_eq_left]
    linarith

lemma apm_m99j03_triangle_one_continuous :
    Continuous (apm_m99j03_triangle 1) := by
  rw [show apm_m99j03_triangle 1 = fun x => max (1 - |x|) 0 by
    funext x
    exact apm_m99j03_triangle_one_eq_max x]
  fun_prop

lemma apm_m99j03_triangle_one_hasCompactSupport :
    HasCompactSupport (apm_m99j03_triangle 1) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  rw [Function.mem_support] at hx
  have hle : |x| ≤ 1 := by
    by_contra h
    have hgt : |x| > 1 := lt_of_not_ge h
    apply hx
    simp [apm_m99j03_triangle, hgt]
  exact (abs_le.mp hle)

/-- The unit triangular profile has total mass one. -/
lemma apm_m99j03_integral_triangle_one :
    (∫ x : ℝ, apm_m99j03_triangle 1 x) = 1 := by
  have hint : MeasureTheory.Integrable (apm_m99j03_triangle 1) :=
    apm_m99j03_triangle_one_continuous.integrable_of_hasCompactSupport
      apm_m99j03_triangle_one_hasCompactSupport
  have hleft : (∫ x : ℝ in (-1)..0, apm_m99j03_triangle 1 x) = 1 / 2 := by
    have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume (-1) 0 :=
      continuous_const.intervalIntegrable _ _
    have hxint : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume (-1) 0 :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => 1 + x)]
    · rw [intervalIntegral.integral_add hc hxint,
        intervalIntegral.integral_const, integral_id]
      norm_num
    · intro x hx
      simp only [Set.mem_uIcc] at hx
      rcases hx with hx | hx
      · rw [apm_m99j03_triangle_one_eq_max, abs_of_nonpos hx.2]
        simp [show 0 ≤ 1 + x by linarith]
      · exfalso; linarith
  have hright : (∫ x : ℝ in 0..1, apm_m99j03_triangle 1 x) = 1 / 2 := by
    have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable _ _
    have hxint : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => 1 - x)]
    · rw [intervalIntegral.integral_sub hc hxint,
        intervalIntegral.integral_const, integral_id]
      norm_num
    · intro x hx
      simp only [Set.mem_uIcc] at hx
      rcases hx with hx | hx
      · rw [apm_m99j03_triangle_one_eq_max, abs_of_nonneg hx.1]
        simp [sub_nonneg.mpr hx.2]
      · exfalso; linarith
  have hinterval : (∫ x : ℝ in (-1)..1, apm_m99j03_triangle 1 x) = 1 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint.intervalIntegrable) (hint.intervalIntegrable), hleft, hright]
    norm_num
  have hcompl : (∫ x : ℝ in (Set.Icc (-1 : ℝ) 1)ᶜ,
      apm_m99j03_triangle 1 x) = 0 := by
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc.compl] with x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have habs : |x| > 1 := by rw [abs_of_neg (by linarith)]; linarith
      simp [apm_m99j03_triangle, habs]
    · have habs : |x| > 1 := by rw [abs_of_pos (by linarith)]; exact hx
      simp [apm_m99j03_triangle, habs]
  have hadd := MeasureTheory.integral_add_compl
    (s := Set.Icc (-1 : ℝ) 1) measurableSet_Icc hint
  have hset : (∫ x : ℝ in Set.Icc (-1 : ℝ) 1,
      apm_m99j03_triangle 1 x) = 1 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hinterval
  rw [hset, hcompl] at hadd
  linarith

lemma apm_m99j03_dilation_integrable
    (ψ φ : ℝ → ℝ) (hψ : Continuous ψ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (n : ℕ) :
    MeasureTheory.Integrable (fun x : ℝ => ψ (x / (n : ℝ)) * φ x) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hψ.comp (continuous_id.div_const (n : ℝ))).mul hφ
  · exact hφc.mul_left

/-- Dilation of a continuous profile converges weakly against a compactly
supported continuous function. -/
lemma apm_m99j03_dilation_tendsto
    (ψ φ : ℝ → ℝ) (hψ : Continuous ψ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x : ℝ, ψ (x / (n : ℝ)) * φ x)
      Filter.atTop (nhds (ψ 0 * ∫ x : ℝ, φ x)) := by
  obtain ⟨R, hR⟩ := hφc.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℝ) R).bddAbove_image hψ.norm.continuousOn
  have hdom : ∀ n : ℕ, ∀ x : ℝ,
      ‖ψ (x / (n : ℝ)) * φ x‖ ≤ C * ‖φ x‖ := by
    intro n x
    by_cases hx : x ∈ Function.support φ
    · have hxt : x ∈ tsupport φ := subset_closure hx
      have hxR : x ∈ Metric.closedBall (0 : ℝ) R := hR hxt
      have hdivR : x / (n : ℝ) ∈ Metric.closedBall (0 : ℝ) R := by
        rw [Metric.mem_closedBall, dist_zero_right] at hxR ⊢
        by_cases hn : n = 0
        · have hR0 : 0 ≤ R := (norm_nonneg x).trans hxR
          simpa [hn] using hR0
        · rw [norm_div]
          have hn1 : 1 ≤ ‖(n : ℝ)‖ := by
            simpa [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using
              (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn) : (1 : ℝ) ≤ n)
          exact (div_le_self (norm_nonneg x) hn1).trans hxR
      calc
        ‖ψ (x / (n : ℝ)) * φ x‖ = ‖ψ (x / (n : ℝ))‖ * ‖φ x‖ := norm_mul _ _
        _ ≤ C * ‖φ x‖ := mul_le_mul_of_nonneg_right
          (hC ⟨_, hdivR, rfl⟩) (norm_nonneg _)
    · simp only [Function.mem_support] at hx
      have hx0 : φ x = 0 := not_ne_iff.mp hx
      simp [hx0]
  have hmeas : ∀ n : ℕ,
      MeasureTheory.AEStronglyMeasurable (fun x : ℝ => ψ (x / (n : ℝ)) * φ x) :=
    fun n => ((hψ.comp (continuous_id.div_const (n : ℝ))).mul hφ).aestronglyMeasurable
  have hmajor : MeasureTheory.Integrable (fun x : ℝ => C * ‖φ x‖) := by
    exact (hφ.norm.integrable_of_hasCompactSupport hφc.norm).const_mul C
  have hlim : ∀ᵐ x : ℝ,
      Filter.Tendsto (fun n : ℕ => ψ (x / (n : ℝ)) * φ x)
        Filter.atTop (nhds (ψ 0 * φ x)) := by
    filter_upwards [] with x
    exact (hψ.continuousAt.tendsto.comp
      (tendsto_const_div_atTop_nhds_zero_nat x)).mul tendsto_const_nhds
  have hi := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : ℝ => C * ‖φ x‖) hmeas hmajor
    (fun n => Filter.Eventually.of_forall (hdom n)) hlim
  simpa [MeasureTheory.integral_const_mul] using hi

theorem apm_m99j03
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∀ φ : ℝ → ℝ, apm_m99j03_IsTestFunction φ →
      Filter.Tendsto
        (fun n : ℕ => ∫ x : ℝ, apm_m99j03_triangle n x * φ x)
        Filter.atTop (nhds (φ 0))) ∧
    (∀ φ : ℝ → ℝ, apm_m99j03_IsTestFunction φ →
      Filter.Tendsto
        (fun n : ℕ => ∫ x : ℝ, apm_m99j03_dipole n x * φ x)
        Filter.atTop (nhds (-deriv φ 0))) ∧
    ∀ φ : ℝ → ℝ, apm_m99j03_IsTestFunction φ →
      Filter.Tendsto
        (fun n : ℕ => ∫ x : ℝ, ψ (x / (n : ℝ)) * φ x)
        Filter.atTop (nhds (ψ 0 * ∫ x : ℝ, φ x)) := by
  have hab :
      (∀ φ : ℝ → ℝ, apm_m99j03_IsTestFunction φ →
        Filter.Tendsto
          (fun n : ℕ => ∫ x : ℝ, apm_m99j03_triangle n x * φ x)
          Filter.atTop (nhds (φ 0))) ∧
      (∀ φ : ℝ → ℝ, apm_m99j03_IsTestFunction φ →
        Filter.Tendsto
          (fun n : ℕ => ∫ x : ℝ, apm_m99j03_dipole n x * φ x)
          Filter.atTop (nhds (-deriv φ 0))) := by
    /-
    Boundary (closer hop 1): part (c) is now fully proved by
    `apm_m99j03_dilation_tendsto`.  Its new domination argument extracts a
    closed-ball bound from `HasCompactSupport φ`, bounds `ψ` on that compact
    ball with `IsCompact.bddAbove_image`, handles `n = 0` explicitly, and
    applies `MeasureTheory.tendsto_integral_of_dominated_convergence` with
    majorant `C * ‖φ x‖`.

    Parts (a) and (b) remain open.  I additionally inspected the exact
    interval-integral APIs used by sibling `a02J03`; they provide scaled
    integral estimates but do not directly rewrite the present raw
    piecewise Lebesgue integrals.  Closure requires proving support reduction
    to `[-1/n,1/n]`, evaluating the triangular weights, and for the dipole
    proving a uniform first-order Taylor remainder for the smooth test
    function.  These two calculations are deliberately kept behind this
    single sorry; the dilation limit no longer depends on it.

    Closer hop 2 compiles the normalization infrastructure for part (a).
    `apm_m99j03_triangle_eq_scaled_profile` proves, for positive `n`,
    `triangle n x = n * triangle 1 (n*x)`. The unit profile is rewritten as
    `max (1-|x|) 0` in `apm_m99j03_triangle_one_eq_max`, and is proved
    continuous and compactly supported in `[-1,1]`. Mathlib source inspection
    found `Measure.integral_comp_mul_left`, so the remaining triangle route is
    exactly: apply that whole-line change of variables, compute the unit
    profile's mass as one, and reuse `apm_m99j03_dilation_tendsto` with the
    roles of profile and test function exchanged.

    The dipole still needs its analogous scaling/cancellation identity and a
    first-order remainder estimate. Closed approximate-identity artifacts
    `a94A03` and `a94J04`, and `ConstructionTargets.RadialMajorantAE`, operate
    in `Lᵖ`/a.e. convolution settings and do not provide this distributional
    first-moment calculation.

    Closer hop 3 proves `apm_m99j03_integral_triangle_one`, completing the
    exact unit-mass calculation for the triangular profile.  The proof reduces
    the whole-line integral to `[-1,1]`, splits at zero, and evaluates the two
    affine pieces as `1/2` each.  Thus part (a) is narrowed to the final
    whole-line change-of-variables assembly using the already compiled scaling
    and dilation lemmas.  Part (b) remains open at the dipole scaling,
    cancellation, and uniform first-order Taylor-remainder argument.
    -/
    sorry
  refine ⟨hab.1, hab.2, ?_⟩
  intro φ hφ
  exact apm_m99j03_dilation_tendsto ψ φ hψ.continuous hφ.1.continuous hφ.2
