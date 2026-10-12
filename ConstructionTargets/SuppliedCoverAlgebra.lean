import ConstructionTargets.CoveringMonodromyCosets
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Small adapters for supplied covering spaces

This file contains only the algebra and topology adapters used by already
supplied covers.  It does not construct a covering from a subgroup.
-/

noncomputable section

namespace ConstructionTargets.SuppliedCoverAlgebra

/-- The fundamental group of the total space of a covering is canonically
equivalent to the range of the induced fundamental-group map. -/
noncomputable def coveringFundamentalGroupEquivRange
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (e : E) :
    FundamentalGroup E e ≃*
      (ConstructionTargets.coveringInducedFundamentalGroupMap cov e).range :=
  MonoidHom.ofInjective
    (ConstructionTargets.coveringInducedFundamentalGroupMap_injective cov e)

/-- If a continuous map becomes an embedding after composition with another
continuous map, then it was already an embedding. -/
theorem isEmbedding_of_comp_eq
    {A E B : Type*} [TopologicalSpace A] [TopologicalSpace E]
    [TopologicalSpace B] (l : A → E) (p : E → B) (i : A → B)
    (hl : Continuous l) (hp : Continuous p)
    (hi : Topology.IsEmbedding i) (h : p ∘ l = i) :
    Topology.IsEmbedding l := by
  rw [← h] at hi
  exact Topology.IsEmbedding.of_comp hl hp hi

/-- Transport the subgroup supplied by a covering through an identification
of the base fundamental group with a finite-rank free group. -/
noncomputable def coveringFundamentalGroupEquivFreeSubgroup
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (e : E) (r : ℕ)
    (base : FundamentalGroup B (p e) ≃* FreeGroup (Fin r)) :
    FundamentalGroup E e ≃*
      (ConstructionTargets.coveringInducedFundamentalGroupMap cov e).range.map
        base.toMonoidHom :=
  (coveringFundamentalGroupEquivRange cov e).trans
    (Subgroup.equivMapOfInjective
      (ConstructionTargets.coveringInducedFundamentalGroupMap cov e).range
      base.toMonoidHom base.injective)

/-- Transport through the base equivalence preserves the subgroup index. -/
theorem coveringFreeSubgroup_index
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) (e : E) (r : ℕ)
    (base : FundamentalGroup B (p e) ≃* FreeGroup (Fin r)) :
    ((ConstructionTargets.coveringInducedFundamentalGroupMap cov e).range.map
      base.toMonoidHom).index =
      (ConstructionTargets.coveringInducedFundamentalGroupMap cov e).range.index := by
  exact Subgroup.index_map_equiv _ base

end ConstructionTargets.SuppliedCoverAlgebra

#print axioms ConstructionTargets.SuppliedCoverAlgebra.coveringFundamentalGroupEquivRange
#print axioms ConstructionTargets.SuppliedCoverAlgebra.isEmbedding_of_comp_eq
#print axioms ConstructionTargets.SuppliedCoverAlgebra.coveringFundamentalGroupEquivFreeSubgroup
#print axioms ConstructionTargets.SuppliedCoverAlgebra.coveringFreeSubgroup_index
