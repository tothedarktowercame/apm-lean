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
  -- Boundary (pass-1 Codex, sustained desk research): searched the Sylow
  -- conjugation action (`Sylow.mulAction`, `Sylow.isPretransitive_of_finite`,
  -- `Sylow.card_sylow_modEq_one`, `Sylow.card_dvd_index`), action kernels
  -- (`MulAction.toPermHom`, `MonoidHom.ker_eq_bot_iff`), simple-group kernel
  -- classification (`Subgroup.Normal.eq_bot_or_eq_top`), permutation transport
  -- (`Equiv.permCongrHom`), coset kernels (`Subgroup.normalCore_eq_ker`), and
  -- alternating-group index/cardinality APIs (`nat_card_alternatingGroup`).
  -- I also inspected all closed artifacts, `LEMMA-INDEX.md`, all of
  -- `ConstructionTargets/`, `YoungL2.lean`, and the partial group-theory
  -- neighbors `b03J01`, `b93A01`, `b96A02`, and `b98A01`; none supplies the
  -- representation-theoretic bridge.
  --
  -- A deeper blocker is that this Mathlib snapshot proves only
  -- `alternatingGroup.isSimpleGroup_five`; its own module header still lists
  -- general simplicity of `alternatingGroup α` as future work.  Thus the third
  -- frozen conjunct for every `n ≥ 5` requires locally developing simplicity of
  -- all `A_n`, in addition to proving faithfulness of the nontrivial Sylow
  -- action, factoring its image through `alternatingGroup`, constructing and
  -- transporting the coset action to `Fin H.index`, proving the factorial
  -- bound, and carrying out the exact Sylow-5 enumeration for order 120.
  -- These are mathematically standard but constitute a major group-theory
  -- development beyond a 15--25 minute pass; no conjunct is asserted via an
  -- unproved shortcut.
  sorry
