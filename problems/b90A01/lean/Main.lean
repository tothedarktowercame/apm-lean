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

/-- Transport a faithful permutation representation on an arbitrary finite
type to the frozen `Fin k` model. -/
lemma apm_b90A01_perm_fin_of_card
    {G α : Type*} [Group G] [Finite α]
    {k : ℕ} (hk : Nat.card α = k)
    (φ : G →* Equiv.Perm α) (hφ : Function.Injective φ) :
    ∃ ψ : G →* Equiv.Perm (Fin k), Function.Injective ψ := by
  let e : α ≃ Fin k := Finite.equivFinOfCardEq hk
  refine ⟨e.permCongrHom.toMonoidHom.comp φ, ?_⟩
  exact e.permCongrHom.injective.comp hφ

/-- In a finite simple group, conjugation on a non-singleton type of Sylow
subgroups is faithful.  The kernel is normal; if it were the whole group, the
pretransitive Sylow action would be trivial on a nontrivial type. -/
lemma apm_b90A01_sylow_action_faithful
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (p : ℕ) (hp : p.Prime) (hk1 : 1 < Nat.card (Sylow p G)) :
    Function.Injective (MulAction.toPermHom G (Sylow p G)) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases (inferInstance : (MulAction.toPermHom G (Sylow p G)).ker.Normal).eq_bot_or_eq_top with
    hker | hker
  · exact hker
  · haveI : Nontrivial (Sylow p G) :=
      Finite.one_lt_card_iff_nontrivial.mp hk1
    obtain ⟨P, Q, hPQ⟩ := exists_pair_ne (Sylow p G)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
    have hgker : g ∈ (MulAction.toPermHom G (Sylow p G)).ker := by
      rw [hker]
      exact Subgroup.mem_top g
    have hgfix : g • P = P := by
      have hgone : MulAction.toPermHom G (Sylow p G) g = 1 :=
        (MonoidHom.mem_ker.mp hgker)
      have := congrArg (fun σ : Equiv.Perm (Sylow p G) => σ P) hgone
      simpa only [MulAction.toPermHom_apply, MulAction.toPerm_apply, coe_one,
        id_eq] using this
    exact False.elim (hPQ (hg ▸ hgfix.symm))

/-- The faithful Sylow conjugation action, transported to the exact `Fin k`
permutation model used in the theorem. -/
lemma apm_b90A01_exists_faithful_sylow_perm
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (p k : ℕ) (hp : p.Prime)
    (hk : Nat.card (Sylow p G) = k) (hk1 : 1 < k) :
    ∃ φ : G →* Equiv.Perm (Fin k), Function.Injective φ := by
  apply apm_b90A01_perm_fin_of_card hk
  exact apm_b90A01_sylow_action_faithful p hp (hk ▸ hk1)

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
  refine ⟨apm_b90A01_exists_faithful_sylow_perm p k hp hk hk1, ?_⟩
  /-
  PARTIAL boundary (closer hop 2): the finite-type transport stage is now
  compiled as `apm_b90A01_perm_fin_of_card`. Once the Sylow conjugation action
  is proved faithful, this lemma turns it directly into the first frozen
  `Fin k` representation using `Finite.equivFinOfCardEq` and
  `Equiv.permCongrHom`.

  Closer hop 2 closes the entire first conjunct in the reusable lemma
  `apm_b90A01_exists_faithful_sylow_perm`. Its new kernel argument uses
  `MonoidHom.normal_ker`, simple-group normal-subgroup classification, and
  Sylow pretransitivity; a top kernel would make the action trivial and
  contradict `1 < Nat.card (Sylow p G)`.

  Renewed source inspection confirms that Mathlib still proves simplicity only
  for `alternatingGroup (Fin 5)`, not all `n ≥ 5`. The remaining first-stage
  bridge is factoring the now-faithful action through the alternating group,
  which requires a parity argument. The third
  conjunct still needs a local general simplicity development for `A_n`, and
  the order-120 conjunct needs the exact Sylow-5 enumeration.

  Earlier pass research: searched the Sylow
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
  -- development; no conjunct is asserted via an unproved shortcut.
  -/
  sorry
