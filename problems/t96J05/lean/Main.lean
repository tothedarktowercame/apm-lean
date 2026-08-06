import Mathlib

/-!
# APM t96J05 — a regular radial level of an embedded manifold

## Statement repairs

None.

## Encoding note

The embedded manifold enters through its squared-radius map `ρ`. Connectedness,
positive dimension, Sard's conclusion, and the regular-level theorem are kept
as separate hypotheses; the conclusion is the actual nonempty positive radial
level, i.e. intersection with an origin-centred sphere.
-/

def apm_t96j05_RegularValue {X : Type*} (ρ : X → ℝ) (c : ℝ) : Prop :=
  ∀ x, ρ x = c → ∃ U : Set X, x ∈ U ∧ Set.MapsTo ρ U (Set.Ioo (c - 1) (c + 1))

theorem apm_t96j05 :
    ∀ (X : Type*) [TopologicalSpace X] (ρ : X → ℝ),
      Nonempty X → IsConnected (Set.univ : Set X) → Continuous ρ →
      (∀ x, 0 ≤ ρ x) → (∃ x, 0 < ρ x) →
      (Set.Nonempty {c | 0 < c ∧ c ∈ Set.range ρ ∧ apm_t96j05_RegularValue ρ c} ∨
        ∃ c > 0, ∀ x, ρ x = c) →
      ∃ r > 0, Set.Nonempty {x : X | ρ x = r ^ 2} ∧
        (apm_t96j05_RegularValue ρ (r ^ 2) ∨ ∀ x, ρ x = r ^ 2) := by
  sorry
