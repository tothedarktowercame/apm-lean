import ConstructionTargets.CircleHomology

noncomputable section

namespace ConstructionTargets.SurfaceSchoenflies

theorem embeddedCircle_isClosed_range
    {M : Type} [TopologicalSpace M] [T2Space M]
    (j : C(Circle, M)) (hj : Topology.IsEmbedding j) :
    IsClosed (Set.range j) := by
  exact (isCompact_range j.continuous).isClosed

def embeddedCircleHomeomorphRange
    {M : Type} [TopologicalSpace M]
    (j : C(Circle, M)) (hj : Topology.IsEmbedding j) :
    Circle ≃ₜ Set.range j :=
  hj.toHomeomorph

theorem embeddedCircle_closedRange_and_homeomorph
    {M : Type} [TopologicalSpace M] [T2Space M]
    (j : C(Circle, M)) (hj : Topology.IsEmbedding j) :
    IsClosed (Set.range j) ∧ Nonempty (Circle ≃ₜ Set.range j) := by
  exact ⟨embeddedCircle_isClosed_range j hj,
    ⟨embeddedCircleHomeomorphRange j hj⟩⟩

abbrev EmbeddedCircleFiniteOpenSubcover
    {M : Type} [TopologicalSpace M] (j : C(Circle, M)) : Prop :=
  ∀ {ι : Type} (U : ι → Set M), (∀ i, IsOpen (U i)) →
    Set.range j ⊆ ⋃ i, U i → ∃ s : Finset ι, Set.range j ⊆ ⋃ i ∈ s, U i

theorem embeddedCircle_finite_open_subcover
    {M : Type} [TopologicalSpace M] (j : C(Circle, M)) :
    EmbeddedCircleFiniteOpenSubcover j := by
  intro ι U hU hcover
  exact (isCompact_range j.continuous).elim_finite_subcover U hU hcover

end ConstructionTargets.SurfaceSchoenflies
