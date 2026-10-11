import ConstructionTargets.PolygonBoundaryDecoderVertices

noncomputable section

namespace ConstructionTargets.PolygonBoundaryDecoderInteriors

open PolygonBoundaryCircleRelations
open PolygonBoundaryEdgeDecoders
open PolygonSixEdgeInteriorUniqueness

def halfOpenToClosed (t : Set.Ico (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨t.1, t.2.1, t.2.2.le⟩

theorem n3EdgeDecode_interior_wellDefined
    (j k : Fin 6) (t u : Set.Ico (0 : ℝ) 1)
    (h : circleEdgePoint j (halfOpenToClosed t) =
      circleEdgePoint k (halfOpenToClosed u)) :
    n3EdgeDecode j (halfOpenToClosed t) =
      n3EdgeDecode k (halfOpenToClosed u) := by
  obtain ⟨rfl, rfl⟩ := circleEdgePoint_interior_injective j k t u h
  rfl

theorem torusCrosscapEdgeDecode_interior_wellDefined
    (j k : Fin 6) (t u : Set.Ico (0 : ℝ) 1)
    (h : circleEdgePoint j (halfOpenToClosed t) =
      circleEdgePoint k (halfOpenToClosed u)) :
    torusCrosscapEdgeDecode j (halfOpenToClosed t) =
      torusCrosscapEdgeDecode k (halfOpenToClosed u) := by
  obtain ⟨rfl, rfl⟩ := circleEdgePoint_interior_injective j k t u h
  rfl

end ConstructionTargets.PolygonBoundaryDecoderInteriors
