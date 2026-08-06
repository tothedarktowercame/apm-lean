import Mathlib

/-!
# APM m94A02

## Statement repairs

None.

## Encoding notes

The dimension is written as `n + 1` so that the largest and smallest entries
of the ordered spectrum have canonical indices `0` and `Fin.last n`.  Complex
eigenvalues of the real matrix are defined using its scalar extension to `ℂ`.
-/

open Matrix Polynomial
open scoped BigOperators

noncomputable def apm_m94a02_symmetricPart {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ)⁻¹ • (A + A.transpose)

def apm_m94a02_IsEigenvalue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℂ) : Prop :=
  ∃ v : Fin n → ℂ, v ≠ 0 ∧
    Matrix.mulVec (A.map (algebraMap ℝ ℂ)) v = lam • v

def apm_m94a02_IsOrderedSpectrum {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, i ≤ j → σ j ≤ σ i) ∧
  Matrix.charpoly B = ∏ i : Fin n, (Polynomial.X - Polynomial.C (σ i))

theorem apm_m94a02
    (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (σ : Fin (n + 1) → ℝ)
    (hσ : apm_m94a02_IsOrderedSpectrum (apm_m94a02_symmetricPart A) σ) :
    (∀ lam : ℂ, apm_m94a02_IsEigenvalue A lam →
      σ (Fin.last n) ≤ lam.re ∧ lam.re ≤ σ 0) ∧
    (A.transpose = -A →
      ∀ lam : ℂ, apm_m94a02_IsEigenvalue A lam → lam.re = 0) := by
  sorry
