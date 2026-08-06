import Mathlib

/-!
# APM m01J06: Loaded-rod extremals and buckling loads

## Statement repairs

The phrase "Based no these results" is read as "Based on these results". No
mathematical repair is made.

## Encoding questions

The source's final request asks whether nontrivial solutions are "expected".
We encode that qualitative conclusion as the standard precise bifurcation
statement: nonzero nonlinear solutions occur arbitrarily close to each
linearized critical load and arbitrarily close to the zero configuration.
-/

open MeasureTheory Set

noncomputable section

def apm_m01J06_energy (lam K : ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∫ s in Icc (0 : ℝ) 1,
    lam * Real.cos (φ s) + (1 / 2 : ℝ) * K * (derivWithin φ (Icc 0 1) s) ^ 2

def apm_m01J06_admissible (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Icc 0 1) ∧ φ 0 = 0

def apm_m01J06_stationary (lam K : ℝ) (φ : ℝ → ℝ) : Prop :=
  apm_m01J06_admissible φ ∧
  ∀ η : ℝ → ℝ, ContDiffOn ℝ 2 η (Icc 0 1) → η 0 = 0 →
    DifferentiableAt ℝ
      (fun ε : ℝ ↦ apm_m01J06_energy lam K (fun s ↦ φ s + ε * η s)) 0 ∧
    deriv (fun ε : ℝ ↦
      apm_m01J06_energy lam K (fun s ↦ φ s + ε * η s)) 0 = 0

def apm_m01J06_nonlinearSolution (lam K : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Icc 0 1) ∧
  φ 0 = 0 ∧ derivWithin φ (Icc 0 1) 1 = 0 ∧
  ∀ s ∈ Ioo (0 : ℝ) 1,
    K * iteratedDerivWithin 2 φ (Icc 0 1) s +
      lam * Real.sin (φ s) = 0

def apm_m01J06_linearMode (lam K : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Icc 0 1) ∧
  φ 0 = 0 ∧ derivWithin φ (Icc 0 1) 1 = 0 ∧
  ∀ s ∈ Ioo (0 : ℝ) 1,
    K * iteratedDerivWithin 2 φ (Icc 0 1) s + lam * φ s = 0

def apm_m01J06_nontrivial (φ : ℝ → ℝ) : Prop :=
  ∃ s ∈ Icc (0 : ℝ) 1, φ s ≠ 0

def apm_m01J06_criticalLoad (K : ℝ) (m : ℕ) : ℝ :=
  K * (((2 * (m : ℝ) + 1) * Real.pi / 2) ^ 2)

def apm_m01J06_isBifurcationLoad (K lamStar : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ lam : ℝ, ∃ φ : ℝ → ℝ,
      0 < lam ∧ |lam - lamStar| < δ ∧
      apm_m01J06_nonlinearSolution lam K φ ∧
      apm_m01J06_nontrivial φ ∧
      ∀ s ∈ Icc (0 : ℝ) 1, |φ s| < δ

theorem apm_m01j06
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    (∀ φ : ℝ → ℝ,
      apm_m01J06_stationary lam K φ →
        apm_m01J06_nonlinearSolution lam K φ) ∧
    apm_m01J06_stationary lam K (fun _ ↦ 0) ∧
    ((∃ φ : ℝ → ℝ,
        apm_m01J06_linearMode lam K φ ∧ apm_m01J06_nontrivial φ) ↔
      ∃ m : ℕ, lam = apm_m01J06_criticalLoad K m) ∧
    (∀ m : ℕ,
      apm_m01J06_isBifurcationLoad K (apm_m01J06_criticalLoad K m)) := by
  sorry
