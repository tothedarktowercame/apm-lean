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
    -/
    sorry
  refine ⟨hab.1, hab.2, ?_⟩
  intro φ hφ
  exact apm_m99j03_dilation_tendsto ψ φ hψ.continuous hφ.1.continuous hφ.2
