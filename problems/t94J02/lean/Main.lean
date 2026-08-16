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
    -- STATEMENT REPAIR (frame-1, 2026-08-16, operator-authorized: Joe's
    -- ruling "if the Lean is incorrect but the original problem is correct,
    -- repair the Lean and redispatch"). Mathlib orders TopologicalSpace with
    -- ⊥ = discrete: σ < τ means τ COARSER. The original conjuncts were both
    -- inverted (counterexample: X=Bool, σ=⊥, τ=⊤ — indiscrete is compact).
    -- Correct maximal-compact/minimal-Hausdorff directions:
    (∀ τ : TopologicalSpace X, τ < σ → ¬@CompactSpace X τ) ∧
    (∀ τ : TopologicalSpace X, σ < τ → ¬@T2Space X τ) := by
  sorry
