import ConstructionTargets.PolygonBoundaryCircleRelations

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonBoundaryVertexClasses

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonTorusCrosscapRelation
open ConstructionTargets.PolygonBoundaryInducedQuotient
open ConstructionTargets.PolygonBoundaryCircleRelations

def zeroIcc : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
def oneIcc : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩

@[simp] theorem reverse_zeroIcc : reverse zeroIcc = oneIcc := by
  apply Subtype.ext
  norm_num [reverse, zeroIcc, oneIcc]

@[simp] theorem reverse_oneIcc : reverse oneIcc = zeroIcc := by
  apply Subtype.ext
  norm_num [reverse, zeroIcc, oneIcc]

theorem edgePoint_one_eq_succ_zero (edgeCount edge : ℕ) :
    edgePoint edgeCount edge oneIcc =
      edgePoint edgeCount (edge + 1) zeroIcc := by
  apply Subtype.ext
  simp only [edgePoint, oneIcc, zeroIcc]
  congr 2
  push_cast
  ring

theorem circleEdgePoint_one_eq_succ_zero (j : ℕ) (hj : j < 5) :
    circleEdgePoint ⟨j, by omega⟩ oneIcc =
      circleEdgePoint ⟨j + 1, by omega⟩ zeroIcc := by
  apply Subtype.ext
  exact congrArg (fun x : Disk => (x : ℂ)) (edgePoint_one_eq_succ_zero 6 j)

def vertex (j : Fin 6) : Circle := circleEdgePoint j zeroIcc

theorem n3_vertex_0_eq_1 :
    n3CircleQuotientMap (vertex 0) = n3CircleQuotientMap (vertex 1) :=
  n3CircleQuotientMap_identifies_a zeroIcc

theorem n3_vertex_1_eq_2 :
    n3CircleQuotientMap (vertex 1) = n3CircleQuotientMap (vertex 2) := by
  calc
    _ = n3CircleQuotientMap (circleEdgePoint 0 oneIcc) := by
      exact congrArg n3CircleQuotientMap
        (circleEdgePoint_one_eq_succ_zero 0 (by norm_num)).symm
    _ = n3CircleQuotientMap (circleEdgePoint 1 oneIcc) :=
      n3CircleQuotientMap_identifies_a oneIcc
    _ = _ := congrArg n3CircleQuotientMap
      (circleEdgePoint_one_eq_succ_zero 1 (by norm_num))

theorem n3_vertex_2_eq_3 :
    n3CircleQuotientMap (vertex 2) = n3CircleQuotientMap (vertex 3) :=
  n3CircleQuotientMap_identifies_b zeroIcc

theorem n3_vertex_3_eq_4 :
    n3CircleQuotientMap (vertex 3) = n3CircleQuotientMap (vertex 4) := by
  calc
    _ = n3CircleQuotientMap (circleEdgePoint 2 oneIcc) := by
      exact congrArg n3CircleQuotientMap
        (circleEdgePoint_one_eq_succ_zero 2 (by norm_num)).symm
    _ = n3CircleQuotientMap (circleEdgePoint 3 oneIcc) :=
      n3CircleQuotientMap_identifies_b oneIcc
    _ = _ := congrArg n3CircleQuotientMap
      (circleEdgePoint_one_eq_succ_zero 3 (by norm_num))

theorem n3_vertex_4_eq_5 :
    n3CircleQuotientMap (vertex 4) = n3CircleQuotientMap (vertex 5) :=
  n3CircleQuotientMap_identifies_c zeroIcc

theorem n3_all_vertices (j : Fin 6) :
    n3CircleQuotientMap (vertex j) = n3CircleQuotientMap (vertex 0) := by
  fin_cases j
  · rfl
  · exact n3_vertex_0_eq_1.symm
  · exact (n3_vertex_1_eq_2.symm.trans n3_vertex_0_eq_1.symm)
  · exact (n3_vertex_2_eq_3.symm.trans
      (n3_vertex_1_eq_2.symm.trans n3_vertex_0_eq_1.symm))
  · exact (n3_vertex_3_eq_4.symm.trans
      (n3_vertex_2_eq_3.symm.trans (n3_vertex_1_eq_2.symm.trans n3_vertex_0_eq_1.symm)))
  · exact (n3_vertex_4_eq_5.symm.trans
      (n3_vertex_3_eq_4.symm.trans (n3_vertex_2_eq_3.symm.trans
        (n3_vertex_1_eq_2.symm.trans n3_vertex_0_eq_1.symm))))

theorem torusCrosscap_vertex_0_eq_3 :
    torusCrosscapCircleQuotientMap (vertex 0) =
      torusCrosscapCircleQuotientMap (vertex 3) := by
  calc
    _ = torusCrosscapCircleQuotientMap
        (circleEdgePoint 2 (reverse zeroIcc)) :=
      torusCrosscapCircleQuotientMap_identifies_a zeroIcc
    _ = _ := by
      simpa using congrArg torusCrosscapCircleQuotientMap
        (circleEdgePoint_one_eq_succ_zero 2 (by norm_num))

theorem torusCrosscap_vertex_1_eq_2 :
    torusCrosscapCircleQuotientMap (vertex 1) =
      torusCrosscapCircleQuotientMap (vertex 2) := by
  calc
    _ = torusCrosscapCircleQuotientMap (circleEdgePoint 0 oneIcc) := by
      exact congrArg torusCrosscapCircleQuotientMap
        (circleEdgePoint_one_eq_succ_zero 0 (by norm_num)).symm
    _ = _ := by simpa [vertex] using
      torusCrosscapCircleQuotientMap_identifies_a oneIcc

theorem torusCrosscap_vertex_1_eq_4 :
    torusCrosscapCircleQuotientMap (vertex 1) =
      torusCrosscapCircleQuotientMap (vertex 4) := by
  calc
    _ = torusCrosscapCircleQuotientMap
        (circleEdgePoint 3 (reverse zeroIcc)) :=
      torusCrosscapCircleQuotientMap_identifies_b zeroIcc
    _ = _ := by
      simpa using congrArg torusCrosscapCircleQuotientMap
        (circleEdgePoint_one_eq_succ_zero 3 (by norm_num))

theorem torusCrosscap_vertex_2_eq_3 :
    torusCrosscapCircleQuotientMap (vertex 2) =
      torusCrosscapCircleQuotientMap (vertex 3) := by
  calc
    _ = torusCrosscapCircleQuotientMap (circleEdgePoint 1 oneIcc) := by
      exact congrArg torusCrosscapCircleQuotientMap
        (circleEdgePoint_one_eq_succ_zero 1 (by norm_num)).symm
    _ = _ := by simpa [vertex] using
      torusCrosscapCircleQuotientMap_identifies_b oneIcc

theorem torusCrosscap_vertex_4_eq_5 :
    torusCrosscapCircleQuotientMap (vertex 4) =
      torusCrosscapCircleQuotientMap (vertex 5) :=
  torusCrosscapCircleQuotientMap_identifies_c zeroIcc

theorem torusCrosscap_all_vertices (j : Fin 6) :
    torusCrosscapCircleQuotientMap (vertex j) =
      torusCrosscapCircleQuotientMap (vertex 0) := by
  fin_cases j
  · rfl
  · exact torusCrosscap_vertex_1_eq_2.trans
      (torusCrosscap_vertex_2_eq_3.trans torusCrosscap_vertex_0_eq_3.symm)
  · exact torusCrosscap_vertex_2_eq_3.trans torusCrosscap_vertex_0_eq_3.symm
  · exact torusCrosscap_vertex_0_eq_3.symm
  · exact torusCrosscap_vertex_1_eq_4.symm.trans
      (torusCrosscap_vertex_1_eq_2.trans
        (torusCrosscap_vertex_2_eq_3.trans torusCrosscap_vertex_0_eq_3.symm))
  · exact torusCrosscap_vertex_4_eq_5.symm.trans
      (torusCrosscap_vertex_1_eq_4.symm.trans
        (torusCrosscap_vertex_1_eq_2.trans
          (torusCrosscap_vertex_2_eq_3.trans torusCrosscap_vertex_0_eq_3.symm)))

end ConstructionTargets.PolygonBoundaryVertexClasses

