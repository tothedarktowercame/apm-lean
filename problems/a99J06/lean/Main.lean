import Mathlib

/-!
# APM a99J06: A holomorphic logarithm on a simply connected domain

## Statement repairs

None.

## Encoding questions

None. Holomorphicity on the open domain is represented by complex
differentiability there, and the source's simple connectivity is encoded by
Mathlib's topological predicate `IsSimplyConnected` on the domain itself.
-/

open Set Complex

theorem apm_a99j06
    (Ω : Set ℂ) (hΩopen : IsOpen Ω) (hΩnonempty : Ω.Nonempty)
    (hΩsc : IsSimplyConnected Ω)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω)
    (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ Ω, f z = Complex.exp (g z) := by
  sorry
