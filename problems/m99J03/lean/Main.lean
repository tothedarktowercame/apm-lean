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
  sorry
