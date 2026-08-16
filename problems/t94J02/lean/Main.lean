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
  have topology_eq_of_compact_to_hausdorff
      (source target : TopologicalSpace X)
      (hc : @CompactSpace X source) (hh : @T2Space X target)
      (hle : source ≤ target) : target = source := by
    have homeo : @IsHomeomorph X X source target id :=
      (@isHomeomorph_iff_continuous_bijective X X source target id hc hh).2
        ⟨continuous_id_of_le hle, Function.bijective_id⟩
    apply le_antisymm
    · exact (@isOpen_implies_isOpen_iff X source target).1 fun s hs ↦ by
        simpa only [Set.image_id] using
          (@IsHomeomorph.isOpenMap X X source target id homeo s hs)
    · exact hle
  constructor
  · intro τ hτ hτcompact
    exact hτ.ne (topology_eq_of_compact_to_hausdorff τ σ hτcompact hhausdorff hτ.le).symm
  · intro τ hτ hτhausdorff
    exact hτ.ne (topology_eq_of_compact_to_hausdorff σ τ hcompact hτhausdorff hτ.le).symm
