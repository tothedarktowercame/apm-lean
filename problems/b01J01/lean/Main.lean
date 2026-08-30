import Mathlib

/-!
# APM b01J01: Normal subgroups, quotients, and Sylow subgroups

## Statement repairs

None.

## Encoding questions

None. `Sp(G)` is represented by Mathlib's type `Sylow p G`. To state the
source's set equality across the different ambient groups `G` and `K`, Sylow
subgroups of `K` are mapped into `G` along `K.subtype`; both sides are then
sets of `Subgroup G`.
-/

open Set
open Pointwise
open scoped Pointwise

noncomputable section

/-- Sylow `p`-subgroups of `K`, regarded as subgroups of the ambient `G`. -/
def apm_b01J01_sylowSubgroupsIn {G : Type} [Group G]
    (p : ℕ) (K : Subgroup G) : Set (Subgroup G) :=
  {Q | ∃ P : Sylow p K, Q = (P : Subgroup K).map K.subtype}

/-- Intersections with `K` of Sylow `p`-subgroups of `G`. -/
def apm_b01J01_sylowTraces {G : Type} [Group G]
    (p : ℕ) (K : Subgroup G) : Set (Subgroup G) :=
  {Q | ∃ P : Sylow p G, Q = (P : Subgroup G) ⊓ K}

/-- The relative-index argument proving part (a).  This reuses
`Subgroup.relIndex_dvd_index_of_normal` from Mathlib's index API. -/
lemma apm_b01j01_prime_dvd_quotient
    {G : Type} [Group G] [Finite G] (H K : Subgroup G) [K.Normal]
    {p : ℕ} (hp : p.Prime) (hpH : p ∣ Nat.card H)
    (hpHK : ¬ p ∣ Nat.card ↑(H ⊓ K)) :
    p ∣ Nat.card (G ⧸ K) := by
  have hcard : Nat.card ↑(H ⊓ K) * K.relIndex H = Nat.card H := by
    let e : (K.subgroupOf H) ≃ ↑(H ⊓ K) :=
      { toFun := fun x ↦ ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun x ↦ ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        left_inv := fun x ↦ rfl
        right_inv := fun x ↦ rfl }
    rw [Subgroup.relIndex, ← Nat.card_congr e]
    exact Subgroup.card_mul_index _
  have hpRel : p ∣ K.relIndex H := by
    exact (hp.dvd_mul.mp (hcard ▸ hpH)).resolve_left hpHK
  simpa only [Subgroup.index_eq_card] using
    hpRel.trans (K.relIndex_dvd_index_of_normal H)

/-- Every Sylow subgroup of `K`, mapped into `G`, is the intersection with
`K` of some ambient Sylow subgroup. -/
lemma apm_b01j01_sylowSubgroupsIn_subset_traces
    {G : Type} [Group G] (p : ℕ) (K : Subgroup G) :
    apm_b01J01_sylowSubgroupsIn p K ⊆ apm_b01J01_sylowTraces p K := by
  intro Q hQ
  rcases hQ with ⟨R, rfl⟩
  obtain ⟨P, hP⟩ := R.exists_comap_subtype_eq
  refine ⟨P, ?_⟩
  rw [← hP]
  ext x
  simp

/-- The numerical quotient conclusion needed in part (b), before extracting an
index-`p` subgroup from the finite abelian quotient. -/
lemma apm_b01j01_prime_dvd_abelianization
    {G : Type} [Group G] [Finite G] (H : Subgroup G)
    {p : ℕ} (hp : p.Prime) (hpH : p ∣ Nat.card H)
    (hpHcomm : ¬ p ∣ Nat.card ↥(H ⊓ commutator G)) :
    p ∣ Nat.card (G ⧸ commutator G) := by
  exact apm_b01j01_prime_dvd_quotient H (commutator G) hp hpH hpHcomm

/-- A prime divisor of the order of a finite abelian group occurs in one
cyclic factor, whose reduction modulo that prime supplies an index-`p`
kernel. -/
lemma apm_b01j01_exists_subgroup_index_prime_of_commutative
    {A : Type} [CommGroup A] [Finite A]
    {p : ℕ} (hp : p.Prime) (hpA : p ∣ Nat.card A) :
    ∃ L : Subgroup A, L.index = p := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ι, inst, n, hn, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  letI (i : ι) : NeZero (n i) := NeZero.of_gt (hn i)
  have hcard : Nat.card A = ∏ i : ι, n i := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hpd : p ∣ ∏ i : ι, n i := hcard ▸ hpA
  obtain ⟨i, hi⟩ :=
    (Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hp) n).mp (by simpa using hpd)
  have hdiv : p ∣ n i := by simpa using hi
  let proj : ((i : ι) → Multiplicative (ZMod (n i))) →*
      Multiplicative (ZMod (n i)) := Pi.evalMonoidHom _ i
  let cast : Multiplicative (ZMod (n i)) →* Multiplicative (ZMod p) :=
    (ZMod.castHom hdiv (ZMod p)).toAddMonoidHom.toMultiplicative
  let f : A →* Multiplicative (ZMod p) := cast.comp (proj.comp e.toMonoidHom)
  refine ⟨f.ker, ?_⟩
  rw [Subgroup.index_ker]
  have hf : Function.Surjective f := by
    exact (ZMod.castHom_surjective hdiv).comp
      ((Function.surjective_eval i).comp e.surjective)
  rw [MonoidHom.range_eq_top.mpr hf]
  simp

/-- The finite-set bookkeeping needed once the trace map has been shown to
have equicardinal fibers.  Keeping this separate prevents the group-action
part of the argument from being mixed with a `Finset.univ` calculation. -/
lemma apm_b01j01_card_eq_card_mul_of_constant_fiber
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (c : ℕ)
    (hc : ∀ b : β, (Finset.univ.filter fun a ↦ f a = b).card = c) :
    Fintype.card α = Fintype.card β * c := by
  rw [← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ)
      (t := Finset.univ) (by simp)]
  simp [hc]

/-- Conjugation by an ambient element restricts to an automorphism of a
normal subgroup. -/
def apm_b01j01_conjNormal {G : Type} [Group G]
    (K : Subgroup G) [K.Normal] (g : G) : K ≃* K where
  toFun x := ⟨g * x * g⁻¹, (inferInstance : K.Normal).conj_mem x.1 x.2 g⟩
  invFun x := ⟨g⁻¹ * x * (g⁻¹)⁻¹,
    (inferInstance : K.Normal).conj_mem x.1 x.2 g⁻¹⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

/-- The intersection of an ambient Sylow subgroup with a normal subgroup is
the ambient image of a Sylow subgroup of the normal subgroup. -/
lemma apm_b01j01_exists_sylow_map_eq_inf
    {G : Type} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (p : ℕ) (hp : p.Prime)
    (P : Sylow p G) :
    ∃ Q : Sylow p K,
      (Q : Subgroup K).map K.subtype = (P : Subgroup G) ⊓ K := by
  letI : Fact p.Prime := ⟨hp⟩
  let R : Sylow p K := default
  obtain ⟨S, hS⟩ := R.exists_comap_subtype_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have hRmap : (R : Subgroup K).map K.subtype = (S : Subgroup G) ⊓ K := by
    rw [← hS]
    ext x
    simp
  have hg' : (P : Subgroup G) = MulAut.conj g • (S : Subgroup G) := by
    rw [← hg]
    rfl
  let a := apm_b01j01_conjNormal K g
  let Q : Sylow p K :=
    R.comapOfInjective a.symm.toMonoidHom a.symm.injective (by simp)
  refine ⟨Q, ?_⟩
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    constructor
    · rw [hg']
      simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [Q, a, apm_b01j01_conjNormal] at hy ⊢
      have : (g⁻¹ * (y : G) * g) ∈ (S : Subgroup G) ⊓ K := by
        rw [← hRmap]
        exact ⟨_, hy, rfl⟩
      exact this.1
    · exact y.2
  · intro hx
    rw [hg'] at hx
    simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
    simp [Q, a, apm_b01j01_conjNormal]
    rw [← hS]
    simpa [MulAut.inv_apply, MulAut.conj_apply, mul_assoc] using hx.1

lemma apm_b01j01_smul_inf_normal
    {G : Type} [Group G] (K : Subgroup G) [K.Normal]
    (p : ℕ) (k : K) (P : Sylow p G) :
    (((k : G) • P : Sylow p G) : Subgroup G) ⊓ K =
      MulAut.conj (k : G) • ((P : Subgroup G) ⊓ K) := by
  ext x
  simp only [Subgroup.mem_inf, Sylow.coe_subgroup_smul,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    simpa [MulAut.inv_apply, MulAut.conj_apply] using
      (inferInstance : K.Normal).conj_mem x hx.2 (k : G)⁻¹
  · intro hx
    refine ⟨hx.1, ?_⟩
    have h := (inferInstance : K.Normal).conj_mem _ hx.2 (k : G)
    simpa [MulAut.inv_apply, mul_assoc] using h

lemma apm_b01j01_smul_sylow_map
    {G : Type} [Group G] (K : Subgroup G)
    (p : ℕ) (k : K) (Q : Sylow p K) :
    ((k • Q : Sylow p K) : Subgroup K).map K.subtype =
      MulAut.conj (k : G) • ((Q : Subgroup K).map K.subtype) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨(MulAut.conj k)⁻¹ y, ?_, ?_⟩
    · simpa only [Sylow.coe_subgroup_smul,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem] using hy
    · rw [← hxy]
      rfl
  · rintro ⟨z, hz, hzx⟩
    refine ⟨MulAut.conj k z, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.inv_apply, MulAut.conj_apply, mul_assoc] using hz
    · have h := congrArg (fun t : G ↦ (k : G) * t * (k : G)⁻¹) hzx
      simpa [MulAut.inv_apply, MulAut.conj_apply, mul_assoc] using h

lemma apm_b01j01_trace_fibers_card_eq
    {G : Type} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (p : ℕ) (hp : p.Prime)
    (Q R : Sylow p K) :
    Nat.card {P : Sylow p G //
      (P : Subgroup G) ⊓ K = (Q : Subgroup K).map K.subtype} =
    Nat.card {P : Sylow p G //
      (P : Subgroup G) ⊓ K = (R : Subgroup K).map K.subtype} := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q R
  let ef : {P : Sylow p G //
      (P : Subgroup G) ⊓ K = (Q : Subgroup K).map K.subtype} ≃
      {P : Sylow p G //
      (P : Subgroup G) ⊓ K = (R : Subgroup K).map K.subtype} :=
    { toFun := fun P ↦ ⟨(k : G) • P, by
        rw [apm_b01j01_smul_inf_normal, P.2,
          ← apm_b01j01_smul_sylow_map, hk]⟩
      invFun := fun P ↦ ⟨((k : G)⁻¹) • (P.1 : Sylow p G), by
        change ((((k⁻¹ : K) : G) • (P.1 : Sylow p G) : Sylow p G) :
          Subgroup G) ⊓ K = _
        rw [apm_b01j01_smul_inf_normal, P.2]
        have hk' : (k⁻¹ : K) • R = Q := by rw [← hk]; simp
        rw [← apm_b01j01_smul_sylow_map K p (k⁻¹ : K), hk']⟩
      left_inv := fun P ↦ by ext; simp
      right_inv := fun P ↦ by ext; simp }
  exact Nat.card_congr ef

/-- Why this unblocks part (d) of `apm_b01j01`: the fibers of the trace map
from ambient Sylow subgroups to Sylow subgroups of a normal subgroup all have
one cardinality, so the ambient Sylow count is the base count times that
fiber cardinality. -/
theorem apm_b01J01_bridge_trace_constant_fiber
    {G : Type} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal]
    (p : ℕ) (hp : p.Prime) :
    ∃ c : ℕ,
      (∀ Q : Sylow p K,
        Nat.card
          {P : Sylow p G //
            (P : Subgroup G) ⊓ K =
              (Q : Subgroup K).map K.subtype} = c) ∧
      Nat.card (Sylow p G) = Nat.card (Sylow p K) * c := by
  letI : Fact p.Prime := ⟨hp⟩
  let Q₀ : Sylow p K := default
  let c := Nat.card
    {P : Sylow p G // (P : Subgroup G) ⊓ K =
      (Q₀ : Subgroup K).map K.subtype}
  have hc : ∀ Q : Sylow p K,
      Nat.card {P : Sylow p G // (P : Subgroup G) ⊓ K =
        (Q : Subgroup K).map K.subtype} = c := by
    intro Q
    exact apm_b01j01_trace_fibers_card_eq K p hp Q Q₀
  refine ⟨c, hc, ?_⟩
  let chooseQ (P : Sylow p G) : Sylow p K :=
    Classical.choose (apm_b01j01_exists_sylow_map_eq_inf K p hp P)
  have chooseQ_spec (P : Sylow p G) :
      (P : Subgroup G) ⊓ K = (chooseQ P : Subgroup K).map K.subtype :=
    (Classical.choose_spec (apm_b01j01_exists_sylow_map_eq_inf K p hp P)).symm
  let e : (Σ Q : Sylow p K, {P : Sylow p G //
      (P : Subgroup G) ⊓ K = (Q : Subgroup K).map K.subtype}) ≃ Sylow p G :=
    { toFun := fun z ↦ z.2.1
      invFun := fun P ↦ ⟨chooseQ P, P, chooseQ_spec P⟩
      left_inv := fun z ↦ by
        rcases z with ⟨Q, P⟩
        have hQ : chooseQ P.1 = Q := by
          apply Sylow.ext
          apply Subgroup.map_injective K.subtype_injective
          exact (chooseQ_spec P.1).symm.trans P.2
        apply Sigma.ext hQ
        rw [Subtype.heq_iff_coe_eq (fun x ↦ by
          change _ = (chooseQ P.1 : Subgroup K).map K.subtype ↔
            _ = (Q : Subgroup K).map K.subtype
          rw [hQ])]
      right_inv := fun P ↦ rfl }
  rw [← Nat.card_congr e, Nat.card_sigma]
  simp_rw [hc]
  simp

theorem apm_b01j01
    (G : Type) [Group G] [Finite G]
    (H K : Subgroup G) [K.Normal]
    (p : ℕ) (hp : p.Prime) :
    (p ∣ Nat.card H → ¬(p ∣ Nat.card ↥(H ⊓ K)) →
      p ∣ Nat.card (G ⧸ K)) ∧
    (p ∣ Nat.card H → ¬(p ∣ Nat.card ↥(H ⊓ commutator G)) →
      ∃ L : Subgroup G, L.index = p) ∧
    apm_b01J01_sylowSubgroupsIn p K =
      apm_b01J01_sylowTraces p K ∧
    Nat.card (Sylow p K) ∣ Nat.card (Sylow p G) := by
  refine ⟨fun hpH hpHK ↦ apm_b01j01_prime_dvd_quotient H K hp hpH hpHK, ?_⟩
  refine ⟨?_, ?_⟩
  · intro hpH hpHcomm
    letI : IsMulCommutative (G ⧸ commutator G) :=
      ⟨⟨(Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl).comm⟩⟩
    obtain ⟨M, hM⟩ := apm_b01j01_exists_subgroup_index_prime_of_commutative hp
      (apm_b01j01_prime_dvd_abelianization H hp hpH hpHcomm)
    refine ⟨M.comap (QuotientGroup.mk' (commutator G)), ?_⟩
    rw [M.index_comap_of_surjective (QuotientGroup.mk'_surjective _), hM]
  · constructor
    · apply Set.Subset.antisymm
      · exact apm_b01j01_sylowSubgroupsIn_subset_traces p K
      · rintro Q ⟨P, rfl⟩
        obtain ⟨R, hR⟩ := apm_b01j01_exists_sylow_map_eq_inf K p hp P
        exact ⟨R, hR.symm⟩
    · obtain ⟨c, hc, hcard⟩ := apm_b01J01_bridge_trace_constant_fiber K p hp
      exact ⟨c, hcard⟩
