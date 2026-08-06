import Mathlib

/-!
# APM b93J03

## Statement repairs

The source omits the necessary assumption that `V` is nonzero. It is added as
`[Nontrivial V]`, since the zero vector space has no eigenvector.

## Encoding questions

None. The ordered basis is indexed by `Fin (finrank k V)`, and upper
triangularity is Mathlib's `Matrix.BlockTriangular id` predicate.
-/

theorem apm_b93j03 :
    ∀ (k V : Type*) [Field k] [IsAlgClosed k] [AddCommGroup V]
        [Module k V] [FiniteDimensional k V] [Nontrivial V]
        (A : Set (V →ₗ[k] V)),
      (∀ a ∈ A, ∀ b ∈ A, a.comp b = b.comp a) →
      (∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, ∃ μ : k, a v = μ • v) ∧
      (∃ basis : Module.Basis (Fin (Module.finrank k V)) k V,
        ∀ a ∈ A, (LinearMap.toMatrix basis basis a).BlockTriangular id) := by
  sorry
