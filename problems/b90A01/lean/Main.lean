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

/-- If a simple subgroup of `Aₙ` has index below `n`, then its normal core
cannot be trivial: otherwise the coset action embeds `Aₙ` in `Sₘ` for
`m < n`, contradicting the factorial cardinalities. -/
lemma apm_b90A01_normalCore_ne_bot_of_index_lt
    (n : ℕ) (hn : 5 ≤ n)
    (H : Subgroup (alternatingGroup (Fin n)))
    [IsSimpleGroup H] (hlt : H.index < n) : H.normalCore ≠ ⊥ := by
  let K : Subgroup H := H.normalCore.subgroupOf H
  haveI : K.Normal := Subgroup.normal_subgroupOf
  rcases (inferInstance : K.Normal).eq_bot_or_eq_top with hK | hK
  · have hcore : H.normalCore = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxK : (⟨x, H.normalCore_le hx⟩ : H) ∈ K := hx
      rw [hK] at hxK
      simpa using hxK
    exfalso
    let f := MulAction.toPermHom (alternatingGroup (Fin n))
      (alternatingGroup (Fin n) ⧸ H)
    have hf : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, ← H.normalCore_eq_ker]
      exact hcore
    have hcardle : Nat.card (alternatingGroup (Fin n)) ≤
        Nat.card (Equiv.Perm (alternatingGroup (Fin n) ⧸ H)) :=
      Nat.card_le_card_of_injective f hf
    rw [Nat.card_perm, ← H.index_eq_card] at hcardle
    have hmle : H.index.factorial ≤ (n - 1).factorial :=
      Nat.factorial_le (by omega)
    have htwo : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
      letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [two_mul_nat_card_alternatingGroup, Nat.card_perm]
      simp
    have hfac : n.factorial ≤ 2 * (n - 1).factorial := by omega
    rw [← Nat.mul_factorial_pred (by omega : n ≠ 0)] at hfac
    have hp : 0 < (n - 1).factorial := Nat.factorial_pos _
    nlinarith
  · intro hb
    have : K = ⊥ := by simp [K, hb]
    exact bot_ne_top (this.symm.trans hK)

/-- Consequently, every putative counterexample to the minimal-index bridge
is a normal subgroup of `Aₙ`.  This isolates the remaining group-theoretic
obligation from the completed cardinality argument. -/
lemma apm_b90A01_normal_of_index_lt
    (n : ℕ) (hn : 5 ≤ n)
    (H : Subgroup (alternatingGroup (Fin n)))
    [IsSimpleGroup H] (hlt : H.index < n) : H.Normal := by
  have hc : H.normalCore ≠ ⊥ :=
    apm_b90A01_normalCore_ne_bot_of_index_lt n hn H hlt
  let K : Subgroup H := H.normalCore.subgroupOf H
  haveI : K.Normal := Subgroup.normal_subgroupOf
  have hKne : K ≠ ⊥ := by
    intro hK
    apply hc
    apply le_bot_iff.mp
    intro x hx
    have hxK : (⟨x, H.normalCore_le hx⟩ : H) ∈ K := hx
    rw [hK] at hxK
    simpa using hxK
  have hKtop : K = ⊤ :=
    (inferInstance : K.Normal).eq_bot_or_eq_top.resolve_left hKne
  have hle : H ≤ H.normalCore := Subgroup.subgroupOf_eq_top.mp hKtop
  have heq : H.normalCore = H := le_antisymm H.normalCore_le hle
  rw [← heq]
  infer_instance

/-- Verified finite kernel for the remaining normal-subgroup argument: every
nonidentity element of `A₅` has a commutator which is a three-cycle. -/
lemma apm_b90A01_exists_threeCycle_commutator_five
    (g : alternatingGroup (Fin 5)) (hg : g ≠ 1) :
    ∃ t : alternatingGroup (Fin 5),
      Equiv.Perm.IsThreeCycle
        ((g * t * g⁻¹ * t⁻¹ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
  have h : ∀ g : alternatingGroup (Fin 5), g ≠ 1 →
      ∃ t : alternatingGroup (Fin 5),
        ((g * t * g⁻¹ * t⁻¹ : alternatingGroup (Fin 5)) :
          Equiv.Perm (Fin 5)).support.card = 3 := by
    set_option maxRecDepth 100000 in
      set_option maxHeartbeats 5000000 in
        decide
  obtain ⟨t, ht⟩ := h g hg
  exact ⟨t, card_support_eq_three_iff.mp ht⟩

set_option maxHeartbeats 5000000

/-- Verified finite kernel for the remaining normal-subgroup argument: every
nonidentity element of `A₆` has a commutator which is a three-cycle. -/
lemma apm_b90A01_exists_threeCycle_commutator_six
    (g : alternatingGroup (Fin 6)) (hg : g ≠ 1) :
    ∃ t : alternatingGroup (Fin 6),
      Equiv.Perm.IsThreeCycle
        ((g * t * g⁻¹ * t⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) := by
  have h : ∀ g : alternatingGroup (Fin 6), g ≠ 1 →
      ∃ t : alternatingGroup (Fin 6),
        ((g * t * g⁻¹ * t⁻¹ : alternatingGroup (Fin 6)) :
          Equiv.Perm (Fin 6)).support.card = 3 := by
    set_option maxRecDepth 100000 in
      set_option maxHeartbeats 5000000 in
        decide
  obtain ⟨t, ht⟩ := h g hg
  exact ⟨t, card_support_eq_three_iff.mp ht⟩

set_option maxHeartbeats 200000

/-- Conjugating a permutation along an equivalence preserves the cardinality
of its support. -/
lemma apm_b90A01_card_support_permCongr
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (p : Equiv.Perm α) :
    (e.permCongr p).support.card = p.support.card := by
  have hs : (e.permCongr p).support = p.support.map e.toEmbedding := by
    ext y
    simp only [Equiv.Perm.mem_support, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      intro heq
      apply hy
      simp [Equiv.permCongr_apply, heq]
    · rintro ⟨x, hx, rfl⟩
      intro heq
      apply hx
      apply e.injective
      simpa [Equiv.permCongr_apply] using heq
  rw [hs, Finset.card_map]

/-- Equivalence transport preserves the three-cycle predicate. -/
lemma apm_b90A01_isThreeCycle_permCongr_iff
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (p : Equiv.Perm α) :
    Equiv.Perm.IsThreeCycle (e.permCongr p) ↔ Equiv.Perm.IsThreeCycle p := by
  rw [← card_support_eq_three_iff,
    ← card_support_eq_three_iff,
    apm_b90A01_card_support_permCongr]

/-- The verified `A₅` commutator kernel transported to an arbitrary
five-element carrier. -/
lemma apm_b90A01_exists_threeCycle_commutator_of_card_five
    {α : Type*} [Fintype α] [DecidableEq α] (hk : Fintype.card α = 5)
    (g : alternatingGroup α) (hg : g ≠ 1) :
    ∃ t : alternatingGroup α,
      Equiv.Perm.IsThreeCycle
        ((g * t * g⁻¹ * t⁻¹ : alternatingGroup α) : Equiv.Perm α) := by
  let e : α ≃ Fin 5 := Fintype.equivFinOfCardEq hk
  let E := e.altCongrHom
  have hEg : E g ≠ 1 := by
    intro h
    apply hg
    exact E.injective (by simpa using h)
  obtain ⟨u, hu⟩ := apm_b90A01_exists_threeCycle_commutator_five (E g) hEg
  let t : alternatingGroup α := E.symm u
  refine ⟨t, ?_⟩
  have hmap : E (g * t * g⁻¹ * t⁻¹) = E g * u * (E g)⁻¹ * u⁻¹ := by
    simp [t, E]
  have hp : e.permCongr
      ((g * t * g⁻¹ * t⁻¹ : alternatingGroup α) : Equiv.Perm α) =
      ((E g * u * (E g)⁻¹ * u⁻¹ : alternatingGroup (Fin 5)) :
        Equiv.Perm (Fin 5)) := by
    simpa [E] using congrArg Subtype.val hmap
  rw [← apm_b90A01_isThreeCycle_permCongr_iff e]
  rw [hp]
  exact hu.cycleType

/-- The verified `A₆` commutator kernel transported to an arbitrary
six-element carrier. -/
lemma apm_b90A01_exists_threeCycle_commutator_of_card_six
    {α : Type*} [Fintype α] [DecidableEq α] (hk : Fintype.card α = 6)
    (g : alternatingGroup α) (hg : g ≠ 1) :
    ∃ t : alternatingGroup α,
      Equiv.Perm.IsThreeCycle
        ((g * t * g⁻¹ * t⁻¹ : alternatingGroup α) : Equiv.Perm α) := by
  let e : α ≃ Fin 6 := Fintype.equivFinOfCardEq hk
  let E := e.altCongrHom
  have hEg : E g ≠ 1 := by
    intro h
    apply hg
    exact E.injective (by simpa using h)
  obtain ⟨u, hu⟩ := apm_b90A01_exists_threeCycle_commutator_six (E g) hEg
  let t : alternatingGroup α := E.symm u
  refine ⟨t, ?_⟩
  have hmap : E (g * t * g⁻¹ * t⁻¹) = E g * u * (E g)⁻¹ * u⁻¹ := by
    simp [t, E]
  have hp : e.permCongr
      ((g * t * g⁻¹ * t⁻¹ : alternatingGroup α) : Equiv.Perm α) =
      ((E g * u * (E g)⁻¹ * u⁻¹ : alternatingGroup (Fin 6)) :
        Equiv.Perm (Fin 6)) := by
    simpa [E] using congrArg Subtype.val hmap
  rw [← apm_b90A01_isThreeCycle_permCongr_iff e]
  rw [hp]
  exact hu.cycleType

/-- A nonidentity element of `Aₙ`, for `n ≥ 5`, fails to commute with
some three-cycle.  The three-cycles generate `Aₙ`, while its center is
trivial. -/
lemma apm_b90A01_exists_threeCycle_not_commute
    {n : ℕ} (hn : 5 ≤ n)
    (g : alternatingGroup (Fin n)) (hg : g ≠ 1) :
    ∃ t : alternatingGroup (Fin n),
      Equiv.Perm.IsThreeCycle (t : Equiv.Perm (Fin n)) ∧ ¬ Commute g t := by
  by_contra h
  push_neg at h
  have hcenter : g ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hall : Commute g x := by
      have hx : x ∈ Subgroup.closure
          {t : alternatingGroup (Fin n) |
            Equiv.Perm.IsThreeCycle (t : Equiv.Perm (Fin n))} := by
        rw [alternatingGroup.closure_isThreeCycles_eq_top]
        exact Subgroup.mem_top x
      induction hx using Subgroup.closure_induction with
      | mem x hx => exact h x hx
      | one => exact Commute.one_right g
      | mul x y _ _ hx hy => exact hx.mul_right hy
      | inv x _ hx => exact hx.inv_right
    exact hall.eq.symm
  rw [alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))] at hcenter
  exact hg (by simpa using hcenter)

/-- Commuting a nonidentity element with a suitable three-cycle produces a
nonidentity element supported on at most six points. -/
lemma apm_b90A01_exists_small_commutator
    {n : ℕ} (hn : 5 ≤ n)
    (g : alternatingGroup (Fin n)) (hg : g ≠ 1) :
    ∃ t : alternatingGroup (Fin n),
      Equiv.Perm.IsThreeCycle (t : Equiv.Perm (Fin n)) ∧
      g * t * g⁻¹ * t⁻¹ ≠ 1 ∧
      ((g * t * g⁻¹ * t⁻¹ : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)).support.card ≤ 6 := by
  obtain ⟨t, ht3, hnc⟩ := apm_b90A01_exists_threeCycle_not_commute hn g hg
  refine ⟨t, ht3, ?_, ?_⟩
  · intro hc
    apply hnc
    exact commutatorElement_eq_one_iff_commute.mp hc
  · change ((g : Equiv.Perm (Fin n)) * (t : Equiv.Perm (Fin n)) *
      (g : Equiv.Perm (Fin n))⁻¹ * (t : Equiv.Perm (Fin n))⁻¹).support.card ≤ 6
    calc
      _ ≤ ((g : Equiv.Perm (Fin n)) * (t : Equiv.Perm (Fin n)) *
          (g : Equiv.Perm (Fin n))⁻¹).support.card +
          ((t : Equiv.Perm (Fin n))⁻¹).support.card :=
        Finset.card_le_card (Equiv.Perm.support_mul_le _ _) |>.trans
          (Finset.card_union_le _ _)
      _ = 3 + 3 := by
        rw [Equiv.Perm.card_support_conj, Equiv.Perm.support_inv, ht3.card_support]
      _ = 6 := by norm_num

/-- Restrict a small-support nonidentity even permutation to a carrier of
exactly `min 6 n` points.  The restriction stays even and nonidentity, and
`ofSubtype` recovers the original permutation. -/
lemma apm_b90A01_restrict_small
    {n : ℕ} (c : alternatingGroup (Fin n)) (hc : c ≠ 1)
    (hcard : (c : Equiv.Perm (Fin n)).support.card ≤ 6) :
    ∃ (s : Finset (Fin n)) (cs : alternatingGroup s),
      s.card = min 6 n ∧ cs ≠ 1 ∧
      Equiv.Perm.ofSubtype (cs : Equiv.Perm s) = (c : Equiv.Perm (Fin n)) := by
  have hsle : (c : Equiv.Perm (Fin n)).support.card ≤ min 6 n := by
    apply le_min hcard
    simpa using (c : Equiv.Perm (Fin n)).support.card_le_univ
  obtain ⟨s, hsubs, hscard⟩ := Finset.exists_superset_card_eq hsle (by simp)
  have hinv : ∀ x, (c : Equiv.Perm (Fin n)) x ∈ s ↔ x ∈ s :=
    Equiv.Perm.isInvariant_of_support_le hsubs
  let cp : Equiv.Perm s := (c : Equiv.Perm (Fin n)).subtypePerm hinv
  have hliftp : Equiv.Perm.ofSubtype cp = (c : Equiv.Perm (Fin n)) := by
    exact Equiv.Perm.ofSubtype_subtypePerm _ fun x hx =>
      hsubs (Equiv.Perm.mem_support.mpr hx)
  have hcpsign : Equiv.Perm.sign cp = 1 := by
    have hs := Equiv.Perm.sign_ofSubtype cp
    rw [hliftp] at hs
    exact hs.symm.trans c.prop
  let cs : alternatingGroup s :=
    ⟨cp, by rwa [Equiv.Perm.mem_alternatingGroup]⟩
  have hlift : Equiv.Perm.ofSubtype (cs : Equiv.Perm s) =
      (c : Equiv.Perm (Fin n)) := by
    exact hliftp
  refine ⟨s, cs, hscard, ?_, hlift⟩
  intro hcs
  apply hc
  apply Subtype.ext
  rw [← hlift, hcs]
  simp

/-- Lift the finite `A₅`/`A₆` kernels back to `Aₙ`: every
nonidentity even permutation supported on at most six points has a
three-cycle commutator in the ambient alternating group. -/
lemma apm_b90A01_exists_threeCycle_commutator_of_small_support
    {n : ℕ} (hn : 5 ≤ n)
    (c : alternatingGroup (Fin n)) (hc : c ≠ 1)
    (hcard : (c : Equiv.Perm (Fin n)).support.card ≤ 6) :
    ∃ t : alternatingGroup (Fin n),
      Equiv.Perm.IsThreeCycle
        ((c * t * c⁻¹ * t⁻¹ : alternatingGroup (Fin n)) :
          Equiv.Perm (Fin n)) := by
  obtain ⟨s, cs, hscard, hcs, hlift⟩ := apm_b90A01_restrict_small c hc hcard
  have hsmin : s.card = 5 ∨ s.card = 6 := by
    by_cases hn5 : n = 5
    · left
      omega
    · right
      omega
  obtain ⟨u, hu⟩ : ∃ u : alternatingGroup s,
      Equiv.Perm.IsThreeCycle
        ((cs * u * cs⁻¹ * u⁻¹ : alternatingGroup s) : Equiv.Perm s) := by
    rcases hsmin with hs5 | hs6
    · exact apm_b90A01_exists_threeCycle_commutator_of_card_five
        (by simpa using hs5) cs hcs
    · exact apm_b90A01_exists_threeCycle_commutator_of_card_six
        (by simpa using hs6) cs hcs
  have husign : Equiv.Perm.sign (Equiv.Perm.ofSubtype (u : Equiv.Perm s)) = 1 := by
    rw [Equiv.Perm.sign_ofSubtype]
    exact u.prop
  let t : alternatingGroup (Fin n) :=
    ⟨Equiv.Perm.ofSubtype (u : Equiv.Perm s), by
      rwa [Equiv.Perm.mem_alternatingGroup]⟩
  refine ⟨t, ?_⟩
  have hcomm :
      (((c * t * c⁻¹ * t⁻¹ : alternatingGroup (Fin n)) :
          Equiv.Perm (Fin n))) =
        Equiv.Perm.ofSubtype
          ((cs * u * cs⁻¹ * u⁻¹ : alternatingGroup s) : Equiv.Perm s) := by
    change (c : Equiv.Perm (Fin n)) * Equiv.Perm.ofSubtype (u : Equiv.Perm s) *
      (c : Equiv.Perm (Fin n))⁻¹ * (Equiv.Perm.ofSubtype (u : Equiv.Perm s))⁻¹ = _
    rw [← hlift]
    simp
  rw [hcomm]
  have hsupp :
      ((cs * u * cs⁻¹ * u⁻¹ : alternatingGroup s) : Equiv.Perm s).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have := hu.card_support
    rw [he] at this
    simp at this
  obtain ⟨a, ha⟩ := hsupp
  have hnodup := hu.nodup_iff_mem_support.mpr ha
  have heq := hu.eq_swap_mul_swap_iff_mem_support.mpr ha
  rw [heq]
  simp only [map_mul, Equiv.Perm.ofSubtype_swap_eq]
  rw [Equiv.swap_comm (a : Fin n)]
  apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
  all_goals grind

lemma apm_b90A01_normal_eq_top
    {n : ℕ} (hn : 5 ≤ n)
    (H : Subgroup (alternatingGroup (Fin n))) [H.Normal]
    (hH : H ≠ ⊥) : H = ⊤ := by
  have hex : ∃ g : alternatingGroup (Fin n), g ∈ H ∧ g ≠ 1 := by
    by_contra h
    push_neg at h
    apply hH
    ext g
    constructor
    · intro hg
      exact h g hg
    · intro hg
      subst g
      exact H.one_mem
  obtain ⟨g, hg, hgne⟩ := hex
  obtain ⟨t, ht, hcne, hcard⟩ :=
    apm_b90A01_exists_small_commutator hn g hgne
  let c : alternatingGroup (Fin n) := g * t * g⁻¹ * t⁻¹
  have hcH : c ∈ H := by
    change g * t * g⁻¹ * t⁻¹ ∈ H
    simpa [mul_assoc] using
      H.mul_mem hg
        ((inferInstance : H.Normal).conj_mem g⁻¹ (H.inv_mem hg) t)
  obtain ⟨u, hu⟩ :=
    apm_b90A01_exists_threeCycle_commutator_of_small_support hn c hcne hcard
  let d : alternatingGroup (Fin n) := c * u * c⁻¹ * u⁻¹
  have hdH : d ∈ H := by
    change c * u * c⁻¹ * u⁻¹ ∈ H
    simpa [mul_assoc] using
      H.mul_mem hcH
        ((inferInstance : H.Normal).conj_mem c⁻¹ (H.inv_mem hcH) u)
  apply top_unique
  rw [← hu.alternating_normalClosure (by simpa using hn)]
  refine normalClosure_le_normal ?_
  simpa [Set.singleton_subset_iff] using hdH

/-- Why this unblocks the third conjunct of `apm_b90a01`: this is the
missing minimal-index theorem for proper simple subgroups of `Aₙ`. Its proof
requires the general simplicity/permutation-action development for alternating
groups beyond the currently packaged `A₅` case. -/
theorem apm_b90A01_bridge_1
    (n : ℕ) (hn : 5 ≤ n)
    (H : Subgroup (alternatingGroup (Fin n)))
    [IsSimpleGroup H] (hH : H ≠ ⊤) :
    n ≤ H.index := by
  by_contra hindex
  have hlt : H.index < n := by omega
  letI : H.Normal := apm_b90A01_normal_of_index_lt n hn H hlt
  apply hH
  apply apm_b90A01_normal_eq_top hn H
  intro hbot
  have hs : Subsingleton H := by
    rw [hbot]
    infer_instance
  exact not_subsingleton H hs

/-- A hypothetical simple group of order `120` has exactly six Sylow
`5`-subgroups.  This packages the numerical part of the Sylow argument for the
remaining order-exclusion bridge. -/
lemma apm_b90A01_card_sylow_five_eq_six
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 120) :
    Nat.card (Sylow 5 G) = 6 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Sylow 5 G := Classical.choice Sylow.nonempty
  have hPcard : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hcard]
    have hv : Nat.factorization 120 5 = 1 := by
      rw [Nat.factorization_def _ (by norm_num)]
      conv_lhs => rw [show 120 = 5 * 24 by norm_num]
      rw [padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [hv]
    norm_num
  have hPnebot : (P : Subgroup G) ≠ ⊥ := by
    apply Sylow.ne_bot_of_dvd_card P
    rw [hcard]
    norm_num
  have hPnetop : (P : Subgroup G) ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hcard] at hPcard
    omega
  have hneone : Nat.card (Sylow 5 G) ≠ 1 := by
    intro h
    letI : Subsingleton (Sylow 5 G) :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    have hn := Sylow.normal_of_subsingleton P
    exact hPnetop (hn.eq_bot_or_eq_top.resolve_left hPnebot)
  have hdvd : Nat.card (Sylow 5 G) ∣ 24 := by
    have hi : P.index = 24 := by
      have hi := P.index_mul_card
      rw [hPcard, hcard] at hi
      omega
    rw [← hi]
    exact Sylow.card_dvd_index P
  have hmod := (card_sylow_modEq_one 5 G).symm
  let s := Nat.card (Sylow 5 G)
  have hspos : 0 < s := Nat.card_pos
  have hsle : s ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  change s ∣ 24 at hdvd
  rw [Nat.modEq_iff_dvd] at hmod
  rcases hmod with ⟨c, hc⟩
  have hcsmall : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
  have hsvals : s = 1 ∨ s = 6 ∨ s = 11 ∨ s = 16 ∨ s = 21 := by
    rcases hcsmall with rfl | rfl | rfl | rfl | rfl <;> omega
  rcases hsvals with hs | hs | hs | hs | hs
  · exact False.elim (hneone (by simpa [s] using hs))
  · simpa [s] using hs
  · rw [hs] at hdvd
    norm_num at hdvd
  · rw [hs] at hdvd
    norm_num at hdvd
  · rw [hs] at hdvd
    norm_num at hdvd

/-- A finite perfect group has no subgroup of index three.  Its coset action
would have perfect image in `S₃`; but `S₃` is solvable, so that image is
trivial, contradicting transitivity on three cosets. -/
lemma apm_b90A01_perfect_no_index_three
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (H : Subgroup G) : H.index ≠ 3 := by
  intro hi
  let f : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H)
  haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
  letI : IsSolvable (Equiv.Perm (G ⧸ H)) := by
    let he : (G ⧸ H) ≃ Fin 3 :=
      Finite.equivFinOfCardEq (by simpa [← H.index_eq_card] using hi)
    letI : IsSolvable (alternatingGroup (Fin 3)) :=
      isSolvable_of_comm (by decide)
    letI : IsSolvable (Equiv.Perm (Fin 3)) := by
      apply solvable_of_ker_le_range
        (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [Equiv.Perm.mem_alternatingGroup]
      exact MonoidHom.mem_ker.mp hx
    exact solvable_of_solvable_injective (f := he.permCongrHom.toMonoidHom)
      he.permCongrHom.injective
  haveI : IsSolvable f.range := inferInstance
  have hrange : Subsingleton f.range := by
    by_contra hn
    letI : Nontrivial f.range := not_subsingleton_iff_nontrivial.mp hn
    exact Group.IsPerfect.not_isSolvable (G := f.range) inferInstance
  have hquot : Subsingleton (G ⧸ H) := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    have hfg : f g = 1 := by
      exact congrArg Subtype.val
        (Subsingleton.elim (⟨f g, g, rfl⟩ : f.range) (⟨1, 1, by simp⟩ : f.range))
    have hx := congrArg (fun σ : Equiv.Perm (G ⧸ H) => σ x) hfg
    simpa [f] using (hg.symm.trans hx).symm
  have hc : Nat.card (G ⧸ H) = 1 := Nat.card_unique
  rw [← H.index_eq_card, hi] at hc
  norm_num at hc

/-- Why this unblocks the fourth conjunct of `apm_b90a01`: this is the exact
Sylow enumeration theorem excluding a finite simple group of order `120`.
It is independent of the preceding faithful alternating representation. -/
theorem apm_b90A01_bridge_2
    (G : Type) [Group G] [Finite G]
    (hcard : Nat.card G = 120) :
    ¬IsSimpleGroup G := by
  intro hs
  letI : IsSimpleGroup G := hs
  have hk : Nat.card (Sylow 5 G) = 6 :=
    apm_b90A01_card_sylow_five_eq_six G hcard
  obtain ⟨ψ, hψ⟩ := apm_b90A01_exists_faithful_sylow_alternating
    (G := G) 5 6 (by norm_num) hk (by norm_num)
  let H : Subgroup (alternatingGroup (Fin 6)) := ψ.range
  have hHcard : Nat.card H = 120 := by
    rw [← hcard]
    exact Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm
  have hAcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hi : H.index = 3 := by
    have hi := H.index_mul_card
    rw [hHcard, hAcard] at hi
    omega
  letI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
  exact apm_b90A01_perfect_no_index_three H hi

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
  exact ⟨fun n hn H _ hH => apm_b90A01_bridge_1 n hn H hH,
    fun G₁ _ _ hcard => apm_b90A01_bridge_2 G₁ hcard⟩
