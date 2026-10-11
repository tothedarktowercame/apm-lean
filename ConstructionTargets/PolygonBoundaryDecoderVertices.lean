import ConstructionTargets.PolygonBoundaryEdgeDecoders

noncomputable section

namespace ConstructionTargets.PolygonBoundaryDecoderVertices

open PointWedgeQuotient
open IntervalEndpointQuotientCircle
open ThreeEndpointLoopsHomeomorph
open PolygonBoundaryThreeLoopSurjectivityReduction
open PolygonBoundaryEdgeDecoders
open PolygonTorusCrosscapRelation
open PolygonBoundaryVertexClasses

def decoderVertex : ThreeEndpointLoops := firstLoopPoint (fromUnitIcc zeroIcc)

theorem firstLoopPoint_one_eq_vertex :
    firstLoopPoint (fromUnitIcc oneIcc) = decoderVertex := by
  apply congrArg (fun x => quotientMap twoEndpointLoopsPoint endpointBase
    (.inl (quotientMap endpointBase endpointBase (.inl x))))
  simpa [fromUnitIcc] using intervalQuotientMap_zero_eq_one.symm

theorem secondLoopPoint_zero_eq_vertex :
    secondLoopPoint (fromUnitIcc zeroIcc) = decoderVertex := by
  apply congrArg (fun x => quotientMap twoEndpointLoopsPoint endpointBase (.inl x))
  exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm

theorem secondLoopPoint_one_eq_vertex :
    secondLoopPoint (fromUnitIcc oneIcc) = decoderVertex := by
  rw [show secondLoopPoint (fromUnitIcc oneIcc) =
      secondLoopPoint (fromUnitIcc zeroIcc) by
    apply congrArg (fun x => quotientMap twoEndpointLoopsPoint endpointBase
      (.inl (quotientMap endpointBase endpointBase (.inr x))))
    simpa [fromUnitIcc] using intervalQuotientMap_zero_eq_one.symm]
  exact secondLoopPoint_zero_eq_vertex

theorem thirdLoopPoint_zero_eq_vertex :
    thirdLoopPoint (fromUnitIcc zeroIcc) = decoderVertex := by
  exact (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm

theorem thirdLoopPoint_one_eq_vertex :
    thirdLoopPoint (fromUnitIcc oneIcc) = decoderVertex := by
  rw [show thirdLoopPoint (fromUnitIcc oneIcc) =
      thirdLoopPoint (fromUnitIcc zeroIcc) by
    apply congrArg (fun x => quotientMap twoEndpointLoopsPoint endpointBase (.inr x))
    simpa [fromUnitIcc] using intervalQuotientMap_zero_eq_one.symm]
  exact thirdLoopPoint_zero_eq_vertex

theorem n3EdgeDecode_endpoints (j : Fin 6) :
    n3EdgeDecode j zeroIcc = decoderVertex ∧
      n3EdgeDecode j oneIcc = decoderVertex := by
  fin_cases j
  · exact ⟨rfl, firstLoopPoint_one_eq_vertex⟩
  · exact ⟨rfl, firstLoopPoint_one_eq_vertex⟩
  · exact ⟨secondLoopPoint_zero_eq_vertex, secondLoopPoint_one_eq_vertex⟩
  · exact ⟨secondLoopPoint_zero_eq_vertex, secondLoopPoint_one_eq_vertex⟩
  · exact ⟨thirdLoopPoint_zero_eq_vertex, thirdLoopPoint_one_eq_vertex⟩
  · exact ⟨thirdLoopPoint_zero_eq_vertex, thirdLoopPoint_one_eq_vertex⟩

theorem torusCrosscapEdgeDecode_endpoints (j : Fin 6) :
    torusCrosscapEdgeDecode j zeroIcc = decoderVertex ∧
      torusCrosscapEdgeDecode j oneIcc = decoderVertex := by
  fin_cases j
  · exact ⟨rfl, firstLoopPoint_one_eq_vertex⟩
  · exact ⟨secondLoopPoint_zero_eq_vertex, secondLoopPoint_one_eq_vertex⟩
  · constructor
    · simpa [reverse, zeroIcc, oneIcc] using firstLoopPoint_one_eq_vertex
    · simp [torusCrosscapEdgeDecode, reverse, zeroIcc, oneIcc, decoderVertex]
  · constructor
    · simpa [reverse, zeroIcc, oneIcc] using secondLoopPoint_one_eq_vertex
    · simpa [reverse, zeroIcc, oneIcc] using secondLoopPoint_zero_eq_vertex
  · exact ⟨thirdLoopPoint_zero_eq_vertex, thirdLoopPoint_one_eq_vertex⟩
  · exact ⟨thirdLoopPoint_zero_eq_vertex, thirdLoopPoint_one_eq_vertex⟩

end ConstructionTargets.PolygonBoundaryDecoderVertices
