import ConstructionTargets.PolygonSixEdgeEndpointNormalization

noncomputable section

namespace ConstructionTargets.PolygonSixEdgeFinalEndpointWrap

open PolygonBoundaryCircleRelations
open PolygonBoundaryVertexClasses
open PolygonSixEdgeCircleCover

theorem addCircle_six_eq_zero :
    ((6 : ℝ) : AddCircle (6 : ℝ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨1, by norm_num⟩

theorem circleEdgePoint_five_one_eq_zero_zero :
    circleEdgePoint (5 : Fin 6) oneIcc = circleEdgePoint (0 : Fin 6) zeroIcc := by
  rw [circleEdgePoint_eq_toCircle, circleEdgePoint_eq_toCircle]
  have hleft :
      ((((5 : Fin 6) : ℕ) : ℝ) + oneIcc.1 : AddCircle (6 : ℝ)) =
        ((6 : ℝ) : AddCircle (6 : ℝ)) := by
    apply congrArg (fun x : ℝ => (x : AddCircle (6 : ℝ)))
    norm_num [oneIcc]
  have hright :
      ((((0 : Fin 6) : ℕ) : ℝ) + zeroIcc.1 : AddCircle (6 : ℝ)) = 0 := by
    norm_num [zeroIcc]
  rw [hleft, addCircle_six_eq_zero, hright]

theorem final_endpoint_has_halfOpen_presentation :
    ∃ (k : Fin 6) (u : Set.Ico (0 : ℝ) 1),
      circleEdgePoint (5 : Fin 6) oneIcc =
        circleEdgePoint k ⟨u.1, u.2.1, u.2.2.le⟩ := by
  exact ⟨0, ⟨0, by norm_num⟩, circleEdgePoint_five_one_eq_zero_zero⟩

end ConstructionTargets.PolygonSixEdgeFinalEndpointWrap
