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

/-- A faithful permutation representation of a noncommutative simple group
has even image.  Indeed, the kernel of its sign character is normal.  If that
kernel were trivial, injectivity into the commutative sign group would force
the source group itself to be commutative. -/
lemma apm_b90A01_factor_faithful_through_alternating
    {G α : Type*} [Group G] [IsSimpleGroup G] [Fintype α] [DecidableEq α]
    (φ : G →* Equiv.Perm α) (hφ : Function.Injective φ)
    (hnc : ∃ a b : G, a * b ≠ b * a) :
    ∃ ψ : G →* alternatingGroup α, Function.Injective ψ := by
  let sgn : G →* ℤˣ := Equiv.Perm.sign.comp φ
  have hker : sgn.ker = ⊤ := by
    rcases (inferInstance : sgn.ker.Normal).eq_bot_or_eq_top with hbot | htop
    · exfalso
      have hsgn : Function.Injective sgn := by
        rw [← MonoidHom.ker_eq_bot_iff]
        exact hbot
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      apply hsgn
      simp [sgn, mul_comm]
    · exact htop
  let ψ : G →* alternatingGroup α := φ.codRestrict (alternatingGroup α) fun g => by
    rw [Equiv.Perm.mem_alternatingGroup]
    have hg : g ∈ sgn.ker := by rw [hker]; exact Subgroup.mem_top g
    exact MonoidHom.mem_ker.mp hg
  exact ⟨ψ, fun _ _ h => hφ (congrArg Subtype.val h)⟩

/-- More than one Sylow subgroup rules out commutativity: in a commutative
group every subgroup is normal, so the conjugation action fixes every Sylow
subgroup, contradicting Sylow conjugacy. -/
lemma apm_b90A01_not_commutative_of_multiple_sylow
    {G : Type*} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (hk1 : 1 < Nat.card (Sylow p G)) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hnc
  push_neg at hnc
  letI : IsMulCommutative G := ⟨⟨hnc⟩⟩
  letI : CommGroup G := CommGroup.ofIsMulCommutative
  letI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (Sylow p G) := Finite.one_lt_card_iff_nontrivial.mp hk1
  obtain ⟨P, Q, hPQ⟩ := exists_pair_ne (Sylow p G)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hgfix : g • P = P := by
    rw [Sylow.smul_eq_iff_mem_normalizer, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  exact hPQ (hg ▸ hgfix.symm)

/-- The Sylow action from the hypotheses lands faithfully in the alternating
group, closing the parity stage of the frozen theorem. -/
lemma apm_b90A01_exists_faithful_sylow_alternating
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (p k : ℕ) (hp : p.Prime)
    (hk : Nat.card (Sylow p G) = k) (hk1 : 1 < k) :
    ∃ ψ : G →* alternatingGroup (Fin k), Function.Injective ψ := by
  obtain ⟨φ, hφ⟩ := apm_b90A01_exists_faithful_sylow_perm p k hp hk hk1
  apply apm_b90A01_factor_faithful_through_alternating φ hφ
  exact apm_b90A01_not_commutative_of_multiple_sylow p hp (hk ▸ hk1)

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
  refine ⟨apm_b90A01_exists_faithful_sylow_perm p k hp hk hk1,
    apm_b90A01_exists_faithful_sylow_alternating p k hp hk hk1, ?_⟩
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
  --
  -- CLOSER HOP 3: the parity bridge and hence the entire second conjunct are
  -- now compiled. `apm_b90A01_not_commutative_of_multiple_sylow` shows that
  -- the hypothesis `1 < Nat.card (Sylow p G)` rules out commutativity: in a
  -- commutative group every Sylow subgroup is normal, while Sylow conjugacy
  -- identifies any two of them. Then
  -- `apm_b90A01_factor_faithful_through_alternating` applies simple-group
  -- normal-kernel classification to the sign character. A trivial sign
  -- kernel would embed `G` into the commutative group `ℤˣ`, contradicting
  -- noncommutativity; therefore the kernel is top and `MonoidHom.codRestrict`
  -- gives the required faithful map into `alternatingGroup (Fin k)`.
  --
  -- Searches beyond hop 2 covered the commutator/perfect-group API, the sign
  -- kernel and alternating-group codomain APIs, and the general alternating-
  -- group source. The first two supplied the local parity proof above. The
  -- source still explicitly lists general simplicity of `A_n` as future work,
  -- and no searched corpus artifact supplies either that theorem or the exact
  -- order-120 Sylow enumeration. Those final two conjuncts remain open.
  -/
  sorry
