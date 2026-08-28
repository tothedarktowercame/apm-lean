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

#print axioms subdivisionChain_obj_eq_refinedRestrictedChain_obj
#print axioms subdivisionRefinementObjectIso

end TwoOpenDescentDatum

end ConstructionTargets.FundamentalGroupoidInsertionChainComparison
