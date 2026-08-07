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
  have hψ_cont : Continuous ψ := hψ.continuous
  have hdilation_pointwise :
      ∀ (φ : ℝ → ℝ) (x : ℝ),
        Filter.Tendsto (fun n : ℕ => ψ (x / (n : ℝ)) * φ x)
          Filter.atTop (nhds (ψ 0 * φ x)) := by
    intro φ x
    have hx : Filter.Tendsto (fun n : ℕ => x / (n : ℝ))
        Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat x
    exact (hψ_cont.continuousAt.tendsto.comp hx).mul tendsto_const_nhds
  /-
  Boundary: pointwise convergence and integrability of every member of the
  dilated profile in part (c) are proved above. Completing (c) requires
  extracting a compact support bound
  from `HasCompactSupport φ` and constructing one integrable majorant for
  `ψ (x / n) * φ x` (including the `n = 0` convention) before applying
  `MeasureTheory.tendsto_integral_of_dominated_convergence`. Parts (a) and
  (b) additionally require explicit interval-integral evaluations and a
  first-order Taylor remainder estimate. I searched those dominated
  convergence, compact-support integrability, interval-integral, and Taylor
  APIs but did not assemble all three weak limits in this pass.
  -/
  sorry
