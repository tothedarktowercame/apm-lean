import ConstructionTargets.FundamentalGroupoidTwoOpenInsertion

/-!
# Object coordinates for the single-insertion chain comparison
-/

open CategoryTheory

noncomputable section

namespace ConstructionTargets.FundamentalGroupoidInsertionChainComparison

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.FundamentalGroupoidTwoOpenInsertion

variable {X : Type*} [TopologicalSpace X] {U V : Set X}
variable {C : Type*} [Category C]

namespace TwoOpenDescentDatum

variable (D : @FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum X _ U V C _)
variable {x y : X} {p : Path x y} {S : PathTwoOpenSubdivision p U V}

/-- Every old chain object is literally the refined chain object selected by
the `succAbove` restriction, after exposing the inserted vertex coordinate. -/
theorem subdivisionChain_obj_eq_refinedRestrictedChain_obj
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 2)) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D S).obj i =
      (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain D ins).obj i := by
  change D.obj (p (S.vertex i)) =
    D.obj (p (PathTwoOpenSubdivision.insertedVertex S ins.segment ins.parameter
      ((PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i)))
  rw [PathTwoOpenSubdivision.insertedVertex_old]

/-- The canonical object-coordinate isomorphism used in every successor
square of the insertion comparison. -/
def subdivisionRefinementObjectIso
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 2)) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D S).obj i ≅
      (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain D ins).obj i :=
  eqToIso (subdivisionChain_obj_eq_refinedRestrictedChain_obj D ins i)

@[simp] theorem subdivisionRefinementObjectIso_hom
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 2)) :
    (subdivisionRefinementObjectIso D ins i).hom =
      eqToHom (subdivisionChain_obj_eq_refinedRestrictedChain_obj D ins i) := rfl

/-- Before the split segment, the skip embedding fixes both endpoints of an
old successor edge. -/
theorem succAbove_old_successor_before
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : i < ins.segment) :
    (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.castSucc =
        i.castSucc.castSucc ∧
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.succ =
        i.succ.castSucc := by
  let pivot₀ := PathTwoOpenSubdivision.insertedSidePosition S ins.segment
  have h₀ : i.castSucc < pivot₀ := by
    apply Fin.mk_lt_mk.mpr
    exact Nat.lt_succ_of_lt hi
  have h₁ : i.succ < pivot₀ := by
    apply Fin.mk_lt_mk.mpr
    exact Nat.succ_lt_succ hi
  constructor
  · simpa [PathTwoOpenSubdivision.insertedVertexPosition, pivot₀] using
      Fin.succAbove_castSucc_of_lt pivot₀ i.castSucc h₀
  · simpa [PathTwoOpenSubdivision.insertedVertexPosition, pivot₀] using
      Fin.succAbove_castSucc_of_lt pivot₀ i.succ h₁

/-- At the split segment, the skip embedding jumps from the old left endpoint
to the old right endpoint after the inserted vertex. -/
theorem succAbove_old_successor_crossing
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
          ins.segment.castSucc = ins.segment.castSucc.castSucc ∧
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove
          ins.segment.succ = ins.segment.succ.succ := by
  let pivot₀ := PathTwoOpenSubdivision.insertedSidePosition S ins.segment
  have hp : pivot₀ = ins.segment.succ := by
    apply Fin.ext
    rfl
  have hlt : ins.segment.castSucc < pivot₀ := by
    rw [hp]
    exact Fin.castSucc_lt_succ
  constructor
  · simpa [PathTwoOpenSubdivision.insertedVertexPosition, pivot₀] using
      Fin.succAbove_castSucc_of_lt pivot₀ ins.segment.castSucc hlt
  · have hp' : PathTwoOpenSubdivision.insertedVertexPosition S ins.segment =
        ins.segment.succ.castSucc := by
      apply Fin.ext
      rfl
    rw [hp']
    exact Fin.succAbove_castSucc_self _

/-- After the split segment, the skip embedding shifts both endpoints by one. -/
theorem succAbove_old_successor_after
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : ins.segment < i) :
    (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.castSucc =
        i.castSucc.succ ∧
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove i.succ =
        i.succ.succ := by
  let pivot₀ := PathTwoOpenSubdivision.insertedSidePosition S ins.segment
  have h₀ : pivot₀ ≤ i.castSucc := by
    apply Fin.mk_le_mk.mpr
    exact Nat.succ_le_of_lt hi
  have h₁ : pivot₀ ≤ i.succ := h₀.trans (Fin.castSucc_le_succ i)
  constructor
  · simpa [PathTwoOpenSubdivision.insertedVertexPosition, pivot₀] using
      Fin.succAbove_castSucc_of_le pivot₀ i.castSucc h₀
  · simpa [PathTwoOpenSubdivision.insertedVertexPosition, pivot₀] using
      Fin.succAbove_castSucc_of_le pivot₀ i.succ h₁

#print axioms subdivisionChain_obj_eq_refinedRestrictedChain_obj
#print axioms subdivisionRefinementObjectIso
#print axioms succAbove_old_successor_before
#print axioms succAbove_old_successor_crossing
#print axioms succAbove_old_successor_after

end TwoOpenDescentDatum

end ConstructionTargets.FundamentalGroupoidInsertionChainComparison
