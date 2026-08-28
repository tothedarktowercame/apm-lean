import ConstructionTargets.FundamentalGroupoidTwoOpenInsertion
import ConstructionTargets.FunctorMapPreorderTransport

/-!
# Object coordinates for the single-insertion chain comparison
-/

open CategoryTheory

noncomputable section

namespace ConstructionTargets.FundamentalGroupoidInsertionChainComparison

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.FundamentalGroupoidTwoOpenInsertion
open ConstructionTargets.FunctorMapPreorderTransport

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

/-- Typed map normalization for the refined chain restricted along the
inserted-vertex skip embedding. -/
theorem refinedRestrictedChain_map_transport
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    {a b : Fin (S.n + 2)} (hab : a ≤ b)
    {a' b' : Fin (S.n + 3)} (ha :
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove a = a')
    (hb :
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment).succAbove b = b') :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE hab) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj ha) ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map (homOfLE (by
            rw [← ha, ← hb]
            exact (Fin.succAboveOrderEmb
              (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment)).monotone hab)) ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj hb).symm := by
  exact comp_map_eq_eqToHom_comp_map_comp_eqToHom
    (Fin.succAboveOrderEmb
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment)).monotone.functor
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
      D ins.refined) (homOfLE hab) _ (by simpa using ha) (by simpa using hb)

/-- Before the insertion, a restricted successor map is the corresponding
full refined successor map with its endpoint transports made explicit. -/
theorem refinedRestrictedChain_map_before
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : i < ins.segment) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE i.castSucc_le_succ) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_before ins i hi).1) ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map (homOfLE
            (Fin.castSucc_le_castSucc_iff.mpr i.castSucc_le_succ)) ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_old_successor_before ins i hi).2).symm := by
  exact refinedRestrictedChain_map_transport D ins i.castSucc_le_succ
    (succAbove_old_successor_before ins i hi).1
    (succAbove_old_successor_before ins i hi).2

/-- After the insertion, a restricted successor map is the corresponding
shifted full refined successor map with explicit endpoint transports. -/
theorem refinedRestrictedChain_map_after
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) (hi : ins.segment < i) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE i.castSucc_le_succ) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_after ins i hi).1) ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map (homOfLE
            (Fin.succ_le_succ_iff.mpr i.castSucc_le_succ)) ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_old_successor_after ins i hi).2).symm := by
  exact refinedRestrictedChain_map_transport D ins i.castSucc_le_succ
    (succAbove_old_successor_after ins i hi).1
    (succAbove_old_successor_after ins i hi).2

/-- At the inserted segment, the restricted successor map is the full refined
map across the two explicit endpoints surrounding the skipped vertex. -/
theorem refinedRestrictedChain_map_crossing
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.refinedRestrictedChain
        D ins).map (homOfLE ins.segment.castSucc_le_succ) =
      eqToHom (congrArg
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).obj (succAbove_old_successor_crossing ins).1) ≫
        (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
          D ins.refined).map (homOfLE (by
            apply Fin.mk_le_mk.mpr
            change ins.segment.val ≤ ins.segment.val + 1 + 1
            omega)) ≫
        eqToHom (congrArg
          (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain
            D ins.refined).obj (succAbove_old_successor_crossing ins).2).symm := by
  exact refinedRestrictedChain_map_transport D ins ins.segment.castSucc_le_succ
    (succAbove_old_successor_crossing ins).1
    (succAbove_old_successor_crossing ins).2

/-- The full refined map exposed in the before case is its adjacent mapped
piece. -/
theorem fullRefined_map_before_eq_mappedPiece
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D ins.refined).map
      (homOfLE (Fin.castSucc_le_castSucc_iff.mpr i.castSucc_le_succ)) =
        D.mappedPiece ins.refined ⟨i.val, by
          rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
          omega⟩ := by
  exact FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.adjacentChain_map_succ
    _ _ i.val (by
      rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
      omega)

/-- The shifted full refined map exposed in the after case is its adjacent
mapped piece. -/
theorem fullRefined_map_after_eq_mappedPiece
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (i : Fin (S.n + 1)) :
    (FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.subdivisionChain D ins.refined).map
      (homOfLE (Fin.succ_le_succ_iff.mpr i.castSucc_le_succ)) =
        D.mappedPiece ins.refined ⟨i.val + 1, by
          rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
          omega⟩ := by
  exact FundamentalGroupoidTwoOpenInsertion.TwoOpenDescentDatum.adjacentChain_map_succ
    _ _ (i.val + 1) (by
      rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n]
      omega)

#print axioms subdivisionChain_obj_eq_refinedRestrictedChain_obj
#print axioms subdivisionRefinementObjectIso
#print axioms succAbove_old_successor_before
#print axioms succAbove_old_successor_crossing
#print axioms succAbove_old_successor_after
#print axioms refinedRestrictedChain_map_transport
#print axioms refinedRestrictedChain_map_before
#print axioms refinedRestrictedChain_map_after
#print axioms refinedRestrictedChain_map_crossing
#print axioms fullRefined_map_before_eq_mappedPiece
#print axioms fullRefined_map_after_eq_mappedPiece

end TwoOpenDescentDatum

end ConstructionTargets.FundamentalGroupoidInsertionChainComparison
