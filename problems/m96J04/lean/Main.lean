import Mathlib

/-!
# APM m96J04

## Statement repairs

None.

## Encoding questions

The Hilbert-space example is stated on two copies of `ℓ²(ℕ,ℝ)`. The Banach-space
example is pinned to the Volterra operator on `C([0,1],ℝ)` by its pointwise
integral formula, rather than represented by an anonymous compact operator.
-/

noncomputable section

abbrev apm_m96j04_H := ℓ²(ℕ, ℝ) × ℓ²(ℕ, ℝ)
abbrev apm_m96j04_C := C(Set.Icc (0 : ℝ) 1, ℝ)

def apm_m96j04_extend (f : apm_m96j04_C) (x : ℝ) : ℝ :=
  if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

theorem apm_m96j04 :
    (∃ A : apm_m96j04_H →L[ℝ] apm_m96j04_H,
      (∀ x y : ℓ²(ℕ, ℝ), A (x, y) = (y, 0)) ∧
      ¬IsCompactOperator A ∧
      ∀ n : ℕ, 2 ≤ n → IsCompactOperator (A ^ n)) ∧
    ∃ V : apm_m96j04_C →L[ℝ] apm_m96j04_C,
      (∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1),
        V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s) ∧
      IsCompactOperator V ∧
      ∀ eigenvalue : ℝ, eigenvalue ≠ 0 →
        ∀ f : apm_m96j04_C, V f = eigenvalue • f → f = 0 := by
  sorry
