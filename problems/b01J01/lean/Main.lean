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
  /-
  Boundary (closer hop 3): `apm_b01j01_prime_dvd_abelianization` now compiles
  the full numerical reduction for part (b): the hypotheses force `p` to
  divide the cardinality of `G ⧸ commutator G`.  The only remaining step in
  that conjunct is extracting a subgroup of index `p` from this finite abelian
  quotient and pulling it back. Searches of finite abelian groups, characters,
  maximal subgroups, and quotient correspondence still found no packaged
  theorem from prime cardinal divisibility to a quotient of order `p`.

  For part (c), the forward inclusion remains compiled in
  `apm_b01j01_sylowSubgroupsIn_subset_traces`. A deeper inspection of
  `Sylow.isPretransitive_of_finite` confirms the intended reverse route:
  extend a Sylow of `K` to an ambient Sylow, conjugate that extension to the
  specified ambient `P`, and use normality to preserve `K`. The missing Lean
  packaging is restricting the ambient conjugation automorphism to `K` and
  transporting the resulting Sylow subtype through the exact map/intersection
  encoding. `IsPGroup.inf_normalizer_sylow` only treats normalizers and does
  not replace this construction. Part (d) then still needs the constant-fiber
  orbit count for the trace map. Searches of `LEMMA-INDEX.md`, construction
  targets, all Sylow siblings, normalizer actions, and subgroup map/comap APIs
  found no packaged versions of these two bridges.
  -/
  sorry
