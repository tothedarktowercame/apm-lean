import ConstructionTargets.PolygonSixEdgeFinalEndpointWrap

open ConstructionTargets

noncomputable section

namespace ConstructionTargets.PolygonBoundaryCircleDecoderWellDefined

open PolygonBoundaryCircleRelations
open PolygonBoundaryEdgeDecoders
open PolygonBoundaryDecoderInteriors
open PolygonBoundaryDecoderVertices
open PolygonSixEdgeCircleCover
open PolygonSixEdgeEndpointNormalization
open PolygonSixEdgeFinalEndpointWrap
open ThreeEndpointLoopsHomeomorph

theorem n3EdgeDecode_halfOpen_normalForm (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    ∃ (k : Fin 6) (u : Set.Ico (0 : ℝ) 1),
      circleEdgePoint j t = circleEdgePoint k (halfOpenToClosed u) ∧
        n3EdgeDecode j t = n3EdgeDecode k (halfOpenToClosed u) := by
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · exact ⟨j, ⟨t, t.2.1, ht⟩, rfl, rfl⟩
  · have ht' : t = PolygonBoundaryVertexClasses.oneIcc := by
      apply Subtype.ext
      exact ht
    subst t
    by_cases hj : (j : ℕ) < 5
    · let k : Fin 6 := ⟨j + 1, by omega⟩
      let u : Set.Ico (0 : ℝ) 1 := ⟨0, by norm_num⟩
      refine ⟨k, u, ?_, ?_⟩
      · exact PolygonBoundaryVertexClasses.circleEdgePoint_one_eq_succ_zero j hj
      · exact (n3EdgeDecode_endpoints j).2.trans
          (n3EdgeDecode_endpoints k).1.symm
    · have hj5 : j = (5 : Fin 6) := by ext; omega
      subst j
      let u : Set.Ico (0 : ℝ) 1 := ⟨0, by norm_num⟩
      refine ⟨0, u, circleEdgePoint_five_one_eq_zero_zero, ?_⟩
      exact (n3EdgeDecode_endpoints 5).2.trans
        (n3EdgeDecode_endpoints 0).1.symm

theorem torusCrosscapEdgeDecode_halfOpen_normalForm
    (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    ∃ (k : Fin 6) (u : Set.Ico (0 : ℝ) 1),
      circleEdgePoint j t = circleEdgePoint k (halfOpenToClosed u) ∧
        torusCrosscapEdgeDecode j t =
          torusCrosscapEdgeDecode k (halfOpenToClosed u) := by
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · exact ⟨j, ⟨t, t.2.1, ht⟩, rfl, rfl⟩
  · have ht' : t = PolygonBoundaryVertexClasses.oneIcc := by
      apply Subtype.ext
      exact ht
    subst t
    by_cases hj : (j : ℕ) < 5
    · let k : Fin 6 := ⟨j + 1, by omega⟩
      let u : Set.Ico (0 : ℝ) 1 := ⟨0, by norm_num⟩
      refine ⟨k, u, ?_, ?_⟩
      · exact PolygonBoundaryVertexClasses.circleEdgePoint_one_eq_succ_zero j hj
      · exact (torusCrosscapEdgeDecode_endpoints j).2.trans
          (torusCrosscapEdgeDecode_endpoints k).1.symm
    · have hj5 : j = (5 : Fin 6) := by ext; omega
      subst j
      let u : Set.Ico (0 : ℝ) 1 := ⟨0, by norm_num⟩
      refine ⟨0, u, circleEdgePoint_five_one_eq_zero_zero, ?_⟩
      exact (torusCrosscapEdgeDecode_endpoints 5).2.trans
        (torusCrosscapEdgeDecode_endpoints 0).1.symm

theorem edgeDecoderPresentationIndependent :
    (∀ (j k : Fin 6) (t u : Set.Icc (0 : ℝ) 1),
      circleEdgePoint j t = circleEdgePoint k u →
        n3EdgeDecode j t = n3EdgeDecode k u) ∧
    (∀ (j k : Fin 6) (t u : Set.Icc (0 : ℝ) 1),
      circleEdgePoint j t = circleEdgePoint k u →
        torusCrosscapEdgeDecode j t = torusCrosscapEdgeDecode k u) := by
  constructor
  · intro j k t u h
    obtain ⟨j', t', hjp, hjd⟩ := n3EdgeDecode_halfOpen_normalForm j t
    obtain ⟨k', u', hkp, hkd⟩ := n3EdgeDecode_halfOpen_normalForm k u
    exact hjd.trans ((n3EdgeDecode_interior_wellDefined j' k' t' u'
      (hjp.symm.trans (h.trans hkp))).trans hkd.symm)
  · intro j k t u h
    obtain ⟨j', t', hjp, hjd⟩ :=
      torusCrosscapEdgeDecode_halfOpen_normalForm j t
    obtain ⟨k', u', hkp, hkd⟩ :=
      torusCrosscapEdgeDecode_halfOpen_normalForm k u
    exact hjd.trans ((torusCrosscapEdgeDecode_interior_wellDefined j' k' t' u'
      (hjp.symm.trans (h.trans hkp))).trans hkd.symm)

def chosenEdge (z : Circle) : Fin 6 :=
  Classical.choose (sixEdgeCircleCover z)

def chosenParameter (z : Circle) : Set.Icc (0 : ℝ) 1 :=
  Classical.choose (Classical.choose_spec (sixEdgeCircleCover z))

theorem chosenEdge_spec (z : Circle) :
    circleEdgePoint (chosenEdge z) (chosenParameter z) = z :=
  Classical.choose_spec (Classical.choose_spec (sixEdgeCircleCover z))

def n3CircleDecode (z : Circle) : ThreeEndpointLoops :=
  n3EdgeDecode (chosenEdge z) (chosenParameter z)

def torusCrosscapCircleDecode (z : Circle) : ThreeEndpointLoops :=
  torusCrosscapEdgeDecode (chosenEdge z) (chosenParameter z)

theorem n3CircleDecode_edge (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    n3CircleDecode (circleEdgePoint j t) = n3EdgeDecode j t := by
  unfold n3CircleDecode
  apply edgeDecoderPresentationIndependent.1
  exact chosenEdge_spec _

theorem torusCrosscapCircleDecode_edge (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    torusCrosscapCircleDecode (circleEdgePoint j t) =
      torusCrosscapEdgeDecode j t := by
  unfold torusCrosscapCircleDecode
  apply edgeDecoderPresentationIndependent.2
  exact chosenEdge_spec _

#print axioms edgeDecoderPresentationIndependent
#print axioms n3CircleDecode_edge
#print axioms torusCrosscapCircleDecode_edge

end ConstructionTargets.PolygonBoundaryCircleDecoderWellDefined
