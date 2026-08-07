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
  Boundary (closer hop 1): part (a) is now fully proved by the helper
  `apm_b01j01_prime_dvd_quotient`.  It uses the relative index
  `[H : H ⊓ K]`, Lagrange's cardinality identity, Euclid's lemma for the
  prime `p`, and `Subgroup.relIndex_dvd_index_of_normal`.

  Mathlib's `Sylow.exists_comap_subtype_eq` proves one direction of part (c):
  every Sylow subgroup of `K` is the pullback of an ambient Sylow subgroup.
  The converse still requires proving that `P ⊓ K` is Sylow in `K` when
  `K` is normal.  No declaration packaging that normal-subgroup restriction,
  nor the constant-fiber/orbit count needed for part (d), was found in
  `Sylow.lean`, `LEMMA-INDEX.md`, closed artifacts, or `ConstructionTargets/`.

  Part (b) remains independent: after applying part (a) to `commutator G`,
  one must extract an index-`p` subgroup from the resulting nontrivial finite
  abelian quotient.  Searches of the finite-abelian and index APIs found no
  theorem providing such a subgroup directly from prime divisibility.
  -/
  sorry
