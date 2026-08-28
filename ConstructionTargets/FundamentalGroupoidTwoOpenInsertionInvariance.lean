import ConstructionTargets.FundamentalGroupoidTwoOpenInsertion

/-!
# A proof-carrying single-vertex refinement
-/

open Set CategoryTheory
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.FundamentalGroupoidTwoOpenInsertionInvariance

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.FundamentalGroupoidTwoOpenRefinement
open ConstructionTargets.FundamentalGroupoidTwoOpenInsertion

variable {X : Type*} [TopologicalSpace X] {U V : Set X}
variable {x y : X} {p : Path x y}

namespace PathTwoOpenSubdivision

open ConstructionTargets.FundamentalGroupoidTwoOpenInsertion.PathTwoOpenSubdivision

variable {S : PathTwoOpenSubdivision p U V}

/-- The inserted vertex tuple starts at the old initial vertex. -/
theorem insertedVertex_zero (ins : SingleVertexInsertion S) :
    insertedVertex S ins.segment ins.parameter 0 = S.vertex 0 := by
  change ins.refined.vertex 0 = S.vertex 0
  rw [ins.refined.vertex_zero, S.vertex_zero]

/-- The inserted vertex tuple ends at the old terminal vertex. -/
theorem insertedVertex_last (ins : SingleVertexInsertion S) :
    insertedVertex S ins.segment ins.parameter (Fin.last (S.n + 2)) =
      S.vertex (Fin.last (S.n + 1)) := by
  change ins.refined.vertex (Fin.last (S.n + 2)) =
    S.vertex (Fin.last (S.n + 1))
  simpa only [SingleVertexInsertion.refined_n, S.vertex_last] using
    ins.refined.vertex_last

end PathTwoOpenSubdivision

#print axioms PathTwoOpenSubdivision.insertedVertex_zero
#print axioms PathTwoOpenSubdivision.insertedVertex_last

end ConstructionTargets.FundamentalGroupoidTwoOpenInsertionInvariance
