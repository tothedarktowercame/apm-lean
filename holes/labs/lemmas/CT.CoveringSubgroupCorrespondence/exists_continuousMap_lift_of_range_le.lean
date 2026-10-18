import Mathlib

/-! Interfaces for the based covering associated to a subgroup of a fundamental group. -/

open Set FundamentalGroup
open scoped Topology

noncomputable section

namespace ConstructionTargets.CoveringSubgroupCorrespondence

/-- A basepoint-local formulation of semilocal simple connectivity. -/
def SemilocallySimplyConnected (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U ∈ 𝓝 x, ∀ γ : Path x x, range γ ⊆ U →
    Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk (Path.refl x)

/-- The explicit coset relation used by the based-path construction.  It does
not require the subgroup to be normal. -/
def subgroupCosetSetoid {G : Type*} [Group G] (H : Subgroup G) : Setoid G where
  r g h := g * h⁻¹ ∈ H
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro g
      simpa using H.one_mem
    · intro g h hgh
      have := H.inv_mem hgh
      simpa [mul_inv_rev] using this
    · intro g h k hgh hhk
      have hm := H.mul_mem hgh hhk
      have heq : (g * h⁻¹) * (h * k⁻¹) = g * k⁻¹ := by group
      rwa [heq] at hm

universe u v

/-- **LIBRARY.** The based-path construction produces a connected covering
whose induced fundamental-group image is exactly `H`, and whose distinguished
fibre is the explicit coset quotient.  The total space lives in the universe
of `X`; `exists_connected_subgroup_cover_of_small` moves it to other universes. -/
theorem exists_connected_subgroup_cover
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    [LocPathConnectedSpace X] (hsl : SemilocallySimplyConnected X)
    (x : X) (H : Subgroup (FundamentalGroup X x)) :
    ∃ (E : Type u) (_ : TopologicalSpace E) (p : E → X) (e : E),
      ∃ hp : IsCoveringMap p, ∃ hE : PathConnectedSpace E, ∃ hpe : p e = x,
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpe).range = H ∧
      Nonempty (FundamentalGroup E e ≃* H) ∧
      Nonempty ((p ⁻¹' ({x} : Set X)) ≃ Quotient (subgroupCosetSetoid H)) := by
  sorry

/-- Universe transport of the construction: when `X` is `v`-small, the same
covering can be realised with total space in `Type v` (apply
`exists_connected_subgroup_cover` to `Shrink X` with the transported topology
and compose with the homeomorphism).  Without `Small.{v} X` this fails: a
covering of a connected base by a nonempty space is surjective. -/
theorem exists_connected_subgroup_cover_of_small
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    [LocPathConnectedSpace X] [Small.{v} X] (hsl : SemilocallySimplyConnected X)
    (x : X) (H : Subgroup (FundamentalGroup X x)) :
    ∃ (E : Type v) (_ : TopologicalSpace E) (p : E → X) (e : E),
      ∃ hp : IsCoveringMap p, ∃ hE : PathConnectedSpace E, ∃ hpe : p e = x,
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpe).range = H ∧
      Nonempty (FundamentalGroup E e ≃* H) ∧
      Nonempty ((p ⁻¹' ({x} : Set X)) ≃ Quotient (subgroupCosetSetoid H)) := by
  sorry

/-- The custom quotient has cardinality equal to Mathlib's subgroup index.
This includes infinite index, for which both `Nat.card` and `index` are zero. -/
theorem natCard_cosetQuotient
    {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card (Quotient (subgroupCosetSetoid H)) = H.index := by
  have hsetoid : subgroupCosetSetoid H = QuotientGroup.rightRel H := by
    ext g h
    rw [QuotientGroup.rightRel_apply]
    constructor
    · intro hgh
      simpa [mul_inv_rev] using H.inv_mem hgh
    · intro hhg
      simpa [mul_inv_rev] using H.inv_mem hhg
  rw [hsetoid]
  exact (Nat.card_congr
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)).trans H.index_eq_card.symm

/-- Index zero is precisely infinitude of the explicit coset quotient. -/
theorem cosetQuotient_infinite_of_index_zero
    {G : Type*} [Group G] (H : Subgroup G) (hindex : H.index = 0) :
    (Set.univ : Set (Quotient (subgroupCosetSetoid H))).Infinite := by
  sorry

/-- Monodromy along a path bijects any two fibres of a covering. -/
theorem covering_fiber_equiv
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PathConnectedSpace X] {p : E → X} (hp : IsCoveringMap p) (x y : X) :
    Nonempty ((p ⁻¹' ({x} : Set X)) ≃ (p ⁻¹' ({y} : Set X))) := by
  obtain ⟨γ⟩ := PathConnectedSpace.joined x y
  let γq : Path.Homotopic.Quotient x y := Quotient.mk'' γ
  exact ⟨Equiv.ofBijective (hp.monodromy γq) (hp.monodromy_bijective γq)⟩

/-- A convenient consequence of the preceding monodromy and coset leaves. -/
theorem every_fiber_infinite_of_coset_equiv
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PathConnectedSpace X] [Group G] {p : E → X} (hp : IsCoveringMap p)
    (x : X) (H : Subgroup G) (hindex : H.index = 0)
    (hcoset : Nonempty ((p ⁻¹' ({x} : Set X)) ≃
      Quotient (subgroupCosetSetoid H))) :
    ∀ y : X, (p ⁻¹' ({y} : Set X)).Infinite := by
  sorry

/-- The standard based lifting criterion, packaged without uniqueness. -/
-- BEGIN SEAT AREA
theorem exists_continuousMap_lift_of_range_le
    {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
    [PathConnectedSpace A] [LocPathConnectedSpace A]
    {p : E → X} (hp : IsCoveringMap p) (f : C(A, X)) (a : A) (e : E)
    (he : p e = f a)
    (hle : (FundamentalGroup.map f a).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range) :
    ∃ lift : C(A, E), ∀ z, p (lift z) = f z := by
  sorry
-- END SEAT AREA

/-- Assembly theorem used by finite-index consumers. -/
theorem connectedCover
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    [LocPathConnectedSpace X] [Small.{v} X] (hsl : SemilocallySimplyConnected X)
    (x : X) (H : Subgroup (FundamentalGroup X x)) :
    ∃ (E : Type v) (_ : TopologicalSpace E) (p : E → X) (e : E),
      IsCoveringMap p ∧ PathConnectedSpace E ∧ p e = x ∧
      Nat.card (p ⁻¹' ({x} : Set X)) = H.index ∧
      Nonempty (FundamentalGroup E e ≃* H) := by
  obtain ⟨E, topE, p, e, hp, hE, hpe, hrange, hpi, hcoset⟩ :=
    exists_connected_subgroup_cover_of_small hsl x H
  refine ⟨E, topE, p, e, hp, hE, hpe, ?_, hpi⟩
  exact Nat.card_congr hcoset.some |>.trans (natCard_cosetQuotient H)

end ConstructionTargets.CoveringSubgroupCorrespondence
