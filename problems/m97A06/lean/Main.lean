import Mathlib

open MeasureTheory

/-!
# APM m97A06 — Euler–Lagrange equation, energy, and Hessian

## Statement repairs

The former part (a) restated the definition of `apm_m97a06_EL` and did not
connect the functional to its Euler–Lagrange equation.  It is replaced by the
first-variation characterization of stationary paths under smooth variations
that vanish at both endpoints.
-/

noncomputable def apm_m97a06_I (T : ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) T,
    derivWithin φ (Set.Icc 0 T) t ^ 2 / 2 - Real.cos (2 * φ t) / 4

def apm_m97a06_stationary (T : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiffOn ℝ 2 η (Set.Icc 0 T) → η 0 = 0 → η T = 0 →
    DifferentiableAt ℝ
      (fun ε : ℝ => apm_m97a06_I T (fun t => φ t + ε * η t)) 0 ∧
    deriv (fun ε : ℝ => apm_m97a06_I T (fun t => φ t + ε * η t)) 0 = 0

def apm_m97a06_EL (T : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) T,
    deriv (fun s => derivWithin φ (Set.Icc 0 T) s) t = Real.sin (2 * φ t) / 2

noncomputable def apm_m97a06_energy (T : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  derivWithin φ (Set.Icc 0 T) t ^ 2 / 2 + Real.cos (2 * φ t) / 4

noncomputable def apm_m97a06_hessian (T : ℝ) (η : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) T, deriv η t ^ 2 + η t ^ 2

theorem apm_m97a06 :
    ∀ T : ℝ, 0 < T →
      (∀ φ : ℝ → ℝ, ContDiffOn ℝ 2 φ (Set.Icc 0 T) →
        (apm_m97a06_stationary T φ ↔ apm_m97a06_EL T φ)) ∧
      (∀ φ, ContDiffOn ℝ 2 φ (Set.Icc 0 T) → apm_m97a06_EL T φ →
        ∃ E, ∀ t ∈ Set.Icc (0 : ℝ) T, apm_m97a06_energy T φ t = E) ∧
      apm_m97a06_EL T (fun _ => 0) ∧
      (∀ η : ℝ → ℝ, η 0 = 0 → η T = 0 →
        deriv (deriv (fun ε : ℝ => apm_m97a06_I T (ε • η))) 0 =
          apm_m97a06_hessian T η) := by
  sorry
