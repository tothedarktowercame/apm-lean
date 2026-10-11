import ConstructionTargets.PolygonBoundaryDecoderInteriors

noncomputable section

namespace ConstructionTargets.PolygonSixEdgeEndpointNormalization

open PolygonBoundaryCircleRelations
open PolygonBoundaryVertexClasses

theorem nonfinal_endpoint_has_halfOpen_presentation (j : ℕ) (hj : j < 5) :
    ∃ (k : Fin 6) (u : Set.Ico (0 : ℝ) 1),
      circleEdgePoint ⟨j, by omega⟩ oneIcc =
        circleEdgePoint k ⟨u.1, u.2.1, u.2.2.le⟩ := by
  exact ⟨⟨j + 1, by omega⟩, ⟨0, by norm_num⟩,
    circleEdgePoint_one_eq_succ_zero j hj⟩

end ConstructionTargets.PolygonSixEdgeEndpointNormalization
