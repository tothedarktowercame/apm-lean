import Mathlib

/-!
# APM a98A06

## Statement repairs

None.

## Encoding questions

A function on `ℂ \ {0}` is represented by an ambient function `ℂ → ℂ` whose
analyticity and agreement conditions are restricted to `{0}ᶜ`. A removable
singularity means that this restriction agrees with a complex-differentiable
function on all of `ℂ`.
-/

theorem apm_a98a06 (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({0}ᶜ : Set ℂ))
    (hbound : ∃ N : Set ℂ, IsOpen N ∧ 0 ∈ N ∧ ∃ C : ℝ,
      ∀ z ∈ N, z ≠ 0 → ‖f z‖ * Real.sqrt ‖z‖ ≤ C) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ Set.EqOn F f ({0}ᶜ : Set ℂ) := by
  sorry
