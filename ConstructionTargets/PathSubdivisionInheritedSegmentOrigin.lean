import ConstructionTargets.PathSubdivisionMergedReconstruction

/-!
# Segment origins along subdivision insertion
-/

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.PathSubdivisionInheritedSegmentOrigin

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenInsertion
open ConstructionTargets.PathSubdivisionInsertionReachability
open ConstructionTargets.PathSubdivisionMergedReconstruction

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}

/-- Every target segment retains a source label and lies inside the
corresponding source parameter interval. -/
structure InheritedSegmentOrigin
    (S R : PathTwoOpenSubdivision p U V) : Prop where
  origin : ∀ k : Fin (R.n + 1), ∃ i : Fin (S.n + 1),
    R.side k = S.side i ∧
    S.vertex i.castSucc ≤ R.vertex k.castSucc ∧
    R.vertex k.succ ≤ S.vertex i.succ

theorem InheritedSegmentOrigin.refl (S : PathTwoOpenSubdivision p U V) :
    InheritedSegmentOrigin S S := by
  refine ⟨fun k ↦ ⟨k, rfl, le_rfl, le_rfl⟩⟩

theorem InheritedSegmentOrigin.trans {S R Q : PathTwoOpenSubdivision p U V}
    (hSR : InheritedSegmentOrigin S R)
    (hRQ : InheritedSegmentOrigin R Q) :
    InheritedSegmentOrigin S Q := by
  refine ⟨fun k ↦ ?_⟩
  obtain ⟨j, hsideQ, hloQ, hhiQ⟩ := hRQ.origin k
  obtain ⟨i, hsideR, hloR, hhiR⟩ := hSR.origin j
  exact ⟨i, hsideQ.trans hsideR, hloR.trans hloQ, hhiQ.trans hhiR⟩

/-- One insertion preserves an exact source-segment origin for every new
segment.  The two split segments both originate in the split old segment. -/
theorem inheritedSegmentOrigin_refined
    {S : PathTwoOpenSubdivision p U V}
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    InheritedSegmentOrigin S ins.refined := by
  refine ⟨fun j ↦ ?_⟩
  let pivot₀ := PathTwoOpenSubdivision.insertedSidePosition S ins.segment
  let pivot := PathTwoOpenSubdivision.insertedVertexPosition S ins.segment
  by_cases hr : j = pivot₀
  · subst j
    refine ⟨ins.segment, PathTwoOpenSubdivision.insertedSide_at S ins.segment,
      ?_, ?_⟩
    · change S.vertex ins.segment.castSucc ≤
        PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter pivot₀.castSucc
      rw [show pivot₀.castSucc = pivot by rfl,
        PathTwoOpenSubdivision.insertedVertex_at]
      exact ins.lower
    · have hv : pivot.succAbove ins.segment.succ = pivot₀.succ := by
        have hp : pivot = pivot₀.castSucc := rfl
        rw [hp]
        have he : pivot₀ = ins.segment.succ := by
          apply Fin.ext
          simp [pivot₀, PathTwoOpenSubdivision.insertedSidePosition]
        subst pivot₀
        exact Fin.succAbove_castSucc_self _
      change PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter
          pivot₀.succ ≤ S.vertex ins.segment.succ
      rw [← hv, PathTwoOpenSubdivision.insertedVertex_old]
  · by_cases hl : j.succ = pivot
    · have hj : j = ins.segment.castSucc := by
        apply Fin.ext
        simpa [pivot, PathTwoOpenSubdivision.insertedVertexPosition,
          PathTwoOpenSubdivision.insertedSidePosition] using congrArg Fin.val hl
      refine ⟨ins.segment, ?_, ?_, ?_⟩
      · subst j
        have hp₀ : pivot₀ = ins.segment.succ := by
          apply Fin.ext
          simp [pivot₀, PathTwoOpenSubdivision.insertedSidePosition]
        have he : pivot₀.succAbove ins.segment = ins.segment.castSucc := by
          rw [hp₀]
          exact Fin.succAbove_succ_self _
        exact (show PathTwoOpenSubdivision.insertedSide S ins.segment
            ins.segment.castSucc = S.side ins.segment by
          rw [← he, PathTwoOpenSubdivision.insertedSide_old])
      · have hv : pivot.succAbove ins.segment.castSucc = j.castSucc := by
          have hlt : ins.segment.castSucc < pivot₀ := by
            apply Fin.mk_lt_mk.mpr
            simp
          simpa [pivot, PathTwoOpenSubdivision.insertedVertexPosition, hj] using
            Fin.succAbove_castSucc_of_lt pivot₀ ins.segment.castSucc hlt
        change S.vertex ins.segment.castSucc ≤
          PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter j.castSucc
        rw [← hv, PathTwoOpenSubdivision.insertedVertex_old]
      · change PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter
          j.succ ≤ S.vertex ins.segment.succ
        rw [hl, PathTwoOpenSubdivision.insertedVertex_at]
        exact ins.upper
    · by_cases hb : j < pivot₀
      · let old := j.castPred (Fin.ne_of_lt (hb.trans_le (Fin.le_last _)))
        refine ⟨old, ?_, ?_, ?_⟩
        · simpa [PathTwoOpenSubdivision.insertedSide, old] using
            Fin.insertNth_apply_below (α := fun _ ↦ Bool) hb
              (S.side ins.segment) S.side
        · have hb₀ : j.castSucc < pivot := by
            apply Fin.mk_lt_mk.mpr
            simpa [pivot, pivot₀, PathTwoOpenSubdivision.insertedVertexPosition] using hb
          have hv : PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter
              j.castSucc = S.vertex old.castSucc := by
            simpa [PathTwoOpenSubdivision.insertedVertex, old] using
              Fin.insertNth_apply_below (α := fun _ ↦ unitInterval) hb₀
                ins.parameter S.vertex
          change S.vertex old.castSucc ≤
            PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter j.castSucc
          rw [hv]
        · have hb₁ : j.succ < pivot := by
            have hle : j.succ ≤ pivot := by
              apply Fin.mk_le_mk.mpr
              simpa [pivot, pivot₀, PathTwoOpenSubdivision.insertedVertexPosition] using hb
            exact lt_of_le_of_ne hle hl
          have hv : PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter
              j.succ = S.vertex old.succ := by
            simpa [PathTwoOpenSubdivision.insertedVertex, old] using
              Fin.insertNth_apply_below (α := fun _ ↦ unitInterval) hb₁
                ins.parameter S.vertex
          change PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter
            j.succ ≤ S.vertex old.succ
          rw [hv]
      · have ha : pivot₀ < j := lt_of_le_of_ne (le_of_not_gt hb) (Ne.symm hr)
        let old := j.pred (Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) ha))
        refine ⟨old, ?_, ?_, ?_⟩
        · simpa [PathTwoOpenSubdivision.insertedSide, old] using
            Fin.insertNth_apply_above (α := fun _ ↦ Bool) ha
              (S.side ins.segment) S.side
        · have ha₀ : pivot < j.castSucc := by
            apply Fin.mk_lt_mk.mpr
            simpa [pivot, pivot₀, PathTwoOpenSubdivision.insertedVertexPosition] using ha
          have hv : PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter
              j.castSucc = S.vertex old.castSucc := by
            simpa [PathTwoOpenSubdivision.insertedVertex, old] using
              Fin.insertNth_apply_above (α := fun _ ↦ unitInterval) ha₀
                ins.parameter S.vertex
          change S.vertex old.castSucc ≤
            PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter j.castSucc
          rw [hv]
        · have ha₀ : pivot < j.castSucc := by
            apply Fin.mk_lt_mk.mpr
            simpa [pivot, pivot₀, PathTwoOpenSubdivision.insertedVertexPosition] using ha
          have ha₁ : pivot < j.succ := ha₀.trans j.castSucc_lt_succ
          have hv : PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter
              j.succ = S.vertex old.succ := by
            simpa [PathTwoOpenSubdivision.insertedVertex, old] using
              Fin.insertNth_apply_above (α := fun _ ↦ unitInterval) ha₁
                ins.parameter S.vertex
          change PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter
            j.succ ≤ S.vertex old.succ
          rw [hv]

theorem inheritedSegmentOrigin_of_reachable
    {S R : PathTwoOpenSubdivision p U V} (h : InsertionReachable S R) :
    InheritedSegmentOrigin S R := by
  induction h with
  | refl S => exact InheritedSegmentOrigin.refl S
  | step ins tail ih =>
      exact (inheritedSegmentOrigin_refined ins).trans ih

theorem leftMergedReconstruction_segmentOrigin
    (S T : PathTwoOpenSubdivision p U V) :
    InheritedSegmentOrigin S (leftMergedReconstruction S T).subdivision :=
  inheritedSegmentOrigin_of_reachable (leftMergedReconstruction_reachable S T)

theorem rightMergedReconstruction_segmentOrigin
    (S T : PathTwoOpenSubdivision p U V) :
    InheritedSegmentOrigin T (rightMergedReconstruction S T).subdivision :=
  inheritedSegmentOrigin_of_reachable (rightMergedReconstruction_reachable S T)

#print axioms inheritedSegmentOrigin_refined
#print axioms inheritedSegmentOrigin_of_reachable
#print axioms leftMergedReconstruction_segmentOrigin
#print axioms rightMergedReconstruction_segmentOrigin

end ConstructionTargets.PathSubdivisionInheritedSegmentOrigin
