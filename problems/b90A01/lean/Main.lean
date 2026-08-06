import Mathlib

/-!
# APM b90A01: Simple groups, Sylow actions, and alternating groups

## Statement repairs

None.

## Encoding questions

None. Being isomorphic to a subgroup is represented by the existence of an
injective group homomorphism. The subgroup in part (c) is an actual subgroup
of `alternatingGroup (Fin k)`, so its index is computed in `Aₖ` itself.
-/

open Equiv Subgroup

noncomputable section

theorem apm_b90a01
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (p k : ℕ) (hp : p.Prime)
    (hk : Nat.card (Sylow p G) = k) (hk1 : 1 < k) :
    (∃ φ : G →* Equiv.Perm (Fin k), Function.Injective φ) ∧
    (∃ ψ : G →* alternatingGroup (Fin k), Function.Injective ψ) ∧
    (∀ (n : ℕ) (hn : 5 ≤ n)
      (H : Subgroup (alternatingGroup (Fin n))),
      IsSimpleGroup H → H ≠ ⊤ → n ≤ H.index) ∧
    ∀ (G₁ : Type) [Group G₁] [Finite G₁],
      Nat.card G₁ = 120 → ¬IsSimpleGroup G₁ := by
  -- Boundary: searched the Sylow conjugation action (`Sylow.mulAction`,
  -- `Sylow.exists_smul_eq`, `MulAction.toPermHom`), simple-group kernel
  -- classification (`Subgroup.Normal.eq_bot_or_eq_top`), permutation transport
  -- (`Equiv.permCongrHom`), and alternating-group index/cardinality APIs.
  -- The missing route is a reusable proof that the nontrivial transitive Sylow
  -- action has trivial kernel, followed by factoring it through `alternatingGroup`
  -- and formalizing the coset-action factorial bound.  The final order-120
  -- contradiction depends on all three pieces, so no conjunct was asserted
  -- without completing that representation-theoretic plumbing.
  sorry
