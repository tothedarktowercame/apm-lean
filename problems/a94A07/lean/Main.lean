import Mathlib

noncomputable section

/-!
# APM a94A07

## Statement repairs

None.

## Encoding notes

An entire function is encoded by `Differentiable ℂ f`, and one-to-one by
`Function.Injective f`.
-/

theorem apm_a94a07
    {f : ℂ → ℂ}
    (hf_entire : Differentiable ℂ f)
    (hf_injective : Function.Injective f) :
    ∃ a₀ a₁ : ℂ, a₁ ≠ 0 ∧ ∀ z : ℂ, f z = a₀ + a₁ * z := by
  sorry
