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

end ConstructionTargets.SurfaceSchoenflies
