import Mathlib

/-!
# APM t94J02

## Statement repairs

None.

## Encoding questions

None. Both topologies are explicit values of `TopologicalSpace X` on the same
underlying type. Compactness and Hausdorffness are evaluated using the explicit
topology arguments of `CompactSpace` and `T2Space`, avoiding any wrapper or
change to the ambient typeclass instance.
-/

theorem apm_t94j02 {X : Type*} (σ : TopologicalSpace X)
    (hcompact : @CompactSpace X σ) (hhausdorff : @T2Space X σ) :
    (∀ τ : TopologicalSpace X, σ < τ → ¬@CompactSpace X τ) ∧
    (∀ τ : TopologicalSpace X, τ < σ → ¬@T2Space X τ) := by
  sorry
