import Mathlib

/-!
# APM a98J04 — symmetry of the real derivative of a holomorphic map

## Statement repairs

None.

## Encoding questions

None. Complex numbers are used directly as the real plane. The requested
matrix symmetry is encoded invariantly: the real derivative commutes with
multiplication by `I`, equivalently its real matrix has the form
`[[a, -b], [b, a]]`.
-/

noncomputable section

def apm_a98J04_HasComplexSymmetry (L : ℂ →L[ℝ] ℂ) : Prop :=
  ∀ z : ℂ, L (Complex.I * z) = Complex.I * L z

def apm_a98J04_g : ℂ → ℂ := fun z ↦ star z

def apm_a98J04_h : ℂ → ℂ := fun z ↦ z.re + (2 * z.im) * Complex.I

theorem apm_a98j04 :
    (∀ (f : ℂ → ℂ) (z : ℂ), DifferentiableAt ℂ f z →
      apm_a98J04_HasComplexSymmetry (fderiv ℝ f z)) ∧
    (∀ z : ℂ, ¬apm_a98J04_HasComplexSymmetry (fderiv ℝ apm_a98J04_g z)) ∧
    (∀ z : ℂ, ¬apm_a98J04_HasComplexSymmetry (fderiv ℝ apm_a98J04_h z)) := by
  sorry
