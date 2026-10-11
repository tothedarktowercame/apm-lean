import ConstructionTargets.PolygonBoundaryCircleDecoderWellDefined

open ConstructionTargets

noncomputable section

namespace ConstructionTargets.PolygonBoundaryCircleDecoderRelationInvariant

open PolygonBoundaryCircleRelations
open PolygonBoundaryCircleDecoderWellDefined
open PolygonBoundaryEdgeDecoders
open PolygonBoundaryGeneratorNormalForms

theorem n3CircleDecode_respects {z w : Circle} (h : N3CircleRel z w) :
    n3CircleDecode z = n3CircleDecode w := by
  rcases (n3CircleRel_iff z w).mp h with
    ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  · rw [n3CircleDecode_edge, n3CircleDecode_edge]
    exact (n3EdgeDecode_generators t).1
  · rw [n3CircleDecode_edge, n3CircleDecode_edge]
    exact (n3EdgeDecode_generators t).2.1
  · rw [n3CircleDecode_edge, n3CircleDecode_edge]
    exact (n3EdgeDecode_generators t).2.2

theorem torusCrosscapCircleDecode_respects {z w : Circle}
    (h : TorusCrosscapCircleRel z w) :
    torusCrosscapCircleDecode z = torusCrosscapCircleDecode w := by
  rcases (torusCrosscapCircleRel_iff z w).mp h with
    ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  · rw [torusCrosscapCircleDecode_edge, torusCrosscapCircleDecode_edge]
    exact (torusCrosscapEdgeDecode_generators t).1
  · rw [torusCrosscapCircleDecode_edge, torusCrosscapCircleDecode_edge]
    exact (torusCrosscapEdgeDecode_generators t).2.1
  · rw [torusCrosscapCircleDecode_edge, torusCrosscapCircleDecode_edge]
    exact (torusCrosscapEdgeDecode_generators t).2.2

#print axioms n3CircleDecode_respects
#print axioms torusCrosscapCircleDecode_respects

end ConstructionTargets.PolygonBoundaryCircleDecoderRelationInvariant
