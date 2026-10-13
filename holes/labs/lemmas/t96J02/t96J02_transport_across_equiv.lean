import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.KleinPresentedGroupCoordinateNormalForm
import ConstructionTargets.DeckGroupQuotientFundamentalGroup

/-! # Blueprint for t96J02

The geometric input identifies the registered Klein-bottle fundamental group
with the already-banked presented/coordinate Klein group.  The subgroup
classification is then purely algebraic. -/

open ConstructionTargets.StatementSurfaceModels
open KleinPresentedGroupCoordinateModel

abbrev T96J02Group := FundamentalGroup KleinBottle (surfacePoint false 2)
abbrev T96J02TorusGroup := Multiplicative (ℤ × ℤ)

abbrev T96J02PresentedGroup := PresentedKleinGroup

/-! The definitions above are the complete shared interface used by the
independent lemma seats. -/

/-- **LIBRARY: `program-2026-10-13-polygon-surface-pi1`.**  The fundamental
group of the frozen Klein polygon is its standard presented group. -/
theorem t96J02_kleinBottle_pi1 :
    Nonempty (T96J02Group ≃* T96J02PresentedGroup) := by
  sorry

/-- **LIBRARY.** Every finite-index subgroup of the coordinate Klein group is
either another Klein group or a rank-two free abelian group. -/
theorem t96J02_presented_finiteIndex_classify :
    ∀ H : Subgroup T96J02PresentedGroup, H.FiniteIndex →
      Nonempty (H ≃* T96J02PresentedGroup) ∨
        Nonempty (H ≃* T96J02TorusGroup) := by
  sorry

/-- The whole presented Klein group realizes the Klein-group alternative. -/
theorem t96J02_presented_self_subgroup :
    ∃ H : Subgroup T96J02PresentedGroup,
      H.FiniteIndex ∧ Nonempty (H ≃* T96J02PresentedGroup) := by
  refine ⟨⊤, ?_, ⟨Subgroup.topEquiv⟩⟩
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  infer_instance

/-- The subgroup with even second coordinate realizes the torus-group
alternative. -/
theorem t96J02_presented_torus_subgroup :
    ∃ H : Subgroup T96J02PresentedGroup,
      H.FiniteIndex ∧ Nonempty (H ≃* T96J02TorusGroup) := by
  sorry

/-- Transport classification and the two witnesses across an arbitrary group
equivalence.  This isolates all `Subgroup.map` and finite-index bookkeeping
from both substantive seats. -/
-- BEGIN SEAT AREA
lemma t96J02_transport_across_equiv_aux_index_map
    {G K : Type*} [Group G] [Group K] (e : G ≃* K) (H : Subgroup G) :
    (H.map (e : G →* K)).index = H.index := by
  have h := Subgroup.relIndex_map_map_of_injective
    (f := (e : G →* K)) H (⊤ : Subgroup G) e.injective
  simpa using h

lemma t96J02_transport_across_equiv_aux_finiteIndex_map
    {G K : Type*} [Group G] [Group K] (e : G ≃* K) (H : Subgroup G)
    (hH : H.FiniteIndex) : (H.map (e : G →* K)).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff,
    t96J02_transport_across_equiv_aux_index_map e H]
  exact Subgroup.finiteIndex_iff.mp hH

theorem t96J02_transport_across_equiv
    {G K A : Type*} [Group G] [Group K] [Group A]
    (e : G ≃* K)
    (hclass : ∀ H : Subgroup K, H.FiniteIndex →
      Nonempty (H ≃* K) ∨ Nonempty (H ≃* A))
    (hK : ∃ H : Subgroup K, H.FiniteIndex ∧ Nonempty (H ≃* K))
    (hA : ∃ H : Subgroup K, H.FiniteIndex ∧ Nonempty (H ≃* A)) :
    (∀ H : Subgroup G, H.FiniteIndex →
      Nonempty (H ≃* G) ∨ Nonempty (H ≃* A)) ∧
    (∃ H : Subgroup G, H.FiniteIndex ∧ Nonempty (H ≃* G)) ∧
    (∃ H : Subgroup G, H.FiniteIndex ∧ Nonempty (H ≃* A)) := by
  constructor
  · intro H hH
    have hm : (H.map (e : G →* K)).FiniteIndex :=
      t96J02_transport_across_equiv_aux_finiteIndex_map e H hH
    rcases hclass (H.map (e : G →* K)) hm with h | h
    · left
      rcases h with ⟨f⟩
      exact ⟨((e.subgroupMap H).trans f).trans e.symm⟩
    · right
      rcases h with ⟨f⟩
      exact ⟨(e.subgroupMap H).trans f⟩
  constructor
  · rcases hK with ⟨H, hH, ⟨f⟩⟩
    let H' : Subgroup G := H.map (e.symm : K →* G)
    refine ⟨H', ?_, ?_⟩
    · exact t96J02_transport_across_equiv_aux_finiteIndex_map e.symm H hH
    · exact ⟨((e.symm.subgroupMap H).symm.trans f).trans e.symm⟩
  · rcases hA with ⟨H, hH, ⟨f⟩⟩
    let H' : Subgroup G := H.map (e.symm : K →* G)
    refine ⟨H', ?_, ?_⟩
    · exact t96J02_transport_across_equiv_aux_finiteIndex_map e.symm H hH
    · exact ⟨(e.symm.subgroupMap H).symm.trans f⟩
-- END SEAT AREA

theorem apm_t96j02 :
    (∀ H : Subgroup T96J02Group, H.FiniteIndex →
      Nonempty (H ≃* T96J02Group) ∨ Nonempty (H ≃* T96J02TorusGroup)) ∧
    (∃ H : Subgroup T96J02Group,
      H.FiniteIndex ∧ Nonempty (H ≃* T96J02Group)) ∧
    (∃ H : Subgroup T96J02Group,
      H.FiniteIndex ∧ Nonempty (H ≃* T96J02TorusGroup)) := by
  obtain ⟨e⟩ := t96J02_kleinBottle_pi1
  exact t96J02_transport_across_equiv e
    t96J02_presented_finiteIndex_classify
    t96J02_presented_self_subgroup
    t96J02_presented_torus_subgroup

#print axioms apm_t96j02
