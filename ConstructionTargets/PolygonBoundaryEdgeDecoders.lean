import ConstructionTargets.PolygonBoundaryGeneratorNormalForms

noncomputable section

namespace ConstructionTargets.PolygonBoundaryEdgeDecoders

open PolygonTorusCrosscapRelation
open PolygonBoundaryThreeLoopSurjectivityReduction
open ThreeEndpointLoopsHomeomorph

def n3EdgeDecode (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) : ThreeEndpointLoops :=
  if j = 0 ∨ j = 1 then firstLoopPoint (fromUnitIcc t)
  else if j = 2 ∨ j = 3 then secondLoopPoint (fromUnitIcc t)
  else thirdLoopPoint (fromUnitIcc t)

def torusCrosscapEdgeDecode (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    ThreeEndpointLoops :=
  if j = 0 then firstLoopPoint (fromUnitIcc t)
  else if j = 2 then firstLoopPoint (fromUnitIcc (reverse t))
  else if j = 1 then secondLoopPoint (fromUnitIcc t)
  else if j = 3 then secondLoopPoint (fromUnitIcc (reverse t))
  else thirdLoopPoint (fromUnitIcc t)

@[simp] theorem n3EdgeDecode_zero (t) : n3EdgeDecode 0 t = firstLoopPoint (fromUnitIcc t) := by simp [n3EdgeDecode]
@[simp] theorem n3EdgeDecode_one (t) : n3EdgeDecode 1 t = firstLoopPoint (fromUnitIcc t) := by simp [n3EdgeDecode]
@[simp] theorem n3EdgeDecode_two (t) : n3EdgeDecode 2 t = secondLoopPoint (fromUnitIcc t) := by simp [n3EdgeDecode]
@[simp] theorem n3EdgeDecode_three (t) : n3EdgeDecode 3 t = secondLoopPoint (fromUnitIcc t) := by simp [n3EdgeDecode]
@[simp] theorem n3EdgeDecode_four (t) : n3EdgeDecode 4 t = thirdLoopPoint (fromUnitIcc t) := by simp [n3EdgeDecode]
@[simp] theorem n3EdgeDecode_five (t) : n3EdgeDecode 5 t = thirdLoopPoint (fromUnitIcc t) := by simp [n3EdgeDecode]

@[simp] theorem torusCrosscapEdgeDecode_zero (t) :
    torusCrosscapEdgeDecode 0 t = firstLoopPoint (fromUnitIcc t) := by simp [torusCrosscapEdgeDecode]
@[simp] theorem torusCrosscapEdgeDecode_one (t) :
    torusCrosscapEdgeDecode 1 t = secondLoopPoint (fromUnitIcc t) := by simp [torusCrosscapEdgeDecode]
@[simp] theorem torusCrosscapEdgeDecode_two (t) :
    torusCrosscapEdgeDecode 2 t = firstLoopPoint (fromUnitIcc (reverse t)) := by simp [torusCrosscapEdgeDecode]
@[simp] theorem torusCrosscapEdgeDecode_three (t) :
    torusCrosscapEdgeDecode 3 t = secondLoopPoint (fromUnitIcc (reverse t)) := by simp [torusCrosscapEdgeDecode]
@[simp] theorem torusCrosscapEdgeDecode_four (t) :
    torusCrosscapEdgeDecode 4 t = thirdLoopPoint (fromUnitIcc t) := by simp [torusCrosscapEdgeDecode]
@[simp] theorem torusCrosscapEdgeDecode_five (t) :
    torusCrosscapEdgeDecode 5 t = thirdLoopPoint (fromUnitIcc t) := by simp [torusCrosscapEdgeDecode]

theorem n3EdgeDecode_generators (t : Set.Icc (0 : ℝ) 1) :
    n3EdgeDecode 0 t = n3EdgeDecode 1 t ∧
    n3EdgeDecode 2 t = n3EdgeDecode 3 t ∧
    n3EdgeDecode 4 t = n3EdgeDecode 5 t := by simp

theorem torusCrosscapEdgeDecode_generators (t : Set.Icc (0 : ℝ) 1) :
    torusCrosscapEdgeDecode 0 t = torusCrosscapEdgeDecode 2 (reverse t) ∧
    torusCrosscapEdgeDecode 1 t = torusCrosscapEdgeDecode 3 (reverse t) ∧
    torusCrosscapEdgeDecode 4 t = torusCrosscapEdgeDecode 5 t := by simp

end ConstructionTargets.PolygonBoundaryEdgeDecoders
