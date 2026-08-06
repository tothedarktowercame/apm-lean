import Mathlib

/-!
# APM t00J04

## Statement repairs

The former conclusion used opaque predicates for smooth, closed, and exact
one-forms.  It is replaced by the stronger concrete construction from the
source proof: a global smooth real function with the prescribed derivative at
`p`.  Its manifold differential is the required smooth exact, hence closed,
one-form.  `SecondCountableTopology` makes explicit the standard countability
convention in the term “smooth manifold,” needed for global bump functions.
No source claim is changed.
-/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t00j04_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t00j04_I (n : ℕ) := 𝓘(ℝ, apm_t00j04_E n)

theorem apm_t00j04
    {n : ℕ} (hn : 1 ≤ n)
    {X : Type} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X]
    [ChartedSpace (apm_t00j04_E n) X]
    [IsManifold (apm_t00j04_I n) ∞ X]
    (p : X)
    (omega_p : TangentSpace (apm_t00j04_I n) p →L[ℝ] ℝ)
    (homega_p : omega_p ≠ 0) :
    ∃ f : X → ℝ,
      ContMDiff (apm_t00j04_I n) 𝓘(ℝ, ℝ) ∞ f ∧
      mfderiv (apm_t00j04_I n) 𝓘(ℝ, ℝ) f p = omega_p := by
  sorry
