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
  -- SKIPPED: holomorphic logarithm on simply connected domain.
  -- Key idea: f'/f holomorphic on Ω ⟹ has primitive G (simply connected ⟹ every
  -- holomorphic function has an antiderivative). Then f·exp(-G) is constant,
  -- adjust to get f = exp(g).
  -- Blocker: Mathlib does not have "every holomorphic function on a simply connected
  -- domain has a primitive" as a ready-to-use theorem.
  -- APIs: `DifferentiableOn`, `IsSimplyConnected`, `Complex.exp` — FOUND,
  --   but the existence of primitives on simply connected domains is NOT in Mathlib.
  sorry
