import ConstructionTargets.FundamentalGroupoidTwoOpenRefinement

/-!
# Inserting one vertex in a subordinate two-open path subdivision

This file constructs the finite-index data for inserting a parameter inside
one segment.  The construction duplicates that segment's cover label; its two
new restricted paths are therefore covered by the banked local split theorem.
-/

open Set CategoryTheory
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.FundamentalGroupoidTwoOpenInsertion

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.FundamentalGroupoidTwoOpenRefinement

variable {X : Type*} [TopologicalSpace X] {U V : Set X}
variable {x y : X} {p : Path x y}

namespace PathTwoOpenSubdivision

/-- The vertex tuple obtained by inserting `t` after the initial endpoint of
segment `k`. -/
def insertedVertex (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) (t : unitInterval) : Fin (S.n + 3) → unitInterval :=
  Fin.insertNth (k.succ.castSucc) t S.vertex

/-- The side tuple obtained by duplicating the label of segment `k`. -/
def insertedSide (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) : Fin (S.n + 2) → Bool :=
  Fin.insertNth k.succ (S.side k) S.side

@[simp] theorem insertedVertex_at (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) (t : unitInterval) :
    insertedVertex S k t k.succ.castSucc = t := by
  simp [insertedVertex]

@[simp] theorem insertedVertex_old (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) (t : unitInterval) (i : Fin (S.n + 2)) :
    insertedVertex S k t (k.succ.castSucc.succAbove i) = S.vertex i := by
  simp [insertedVertex]

@[simp] theorem insertedSide_at (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) : insertedSide S k k.succ = S.side k := by
  simp [insertedSide]

@[simp] theorem insertedSide_old (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) (i : Fin (S.n + 1)) :
    insertedSide S k (k.succ.succAbove i) = S.side i := by
  simp [insertedSide]

/-- Proof-carrying insertion data.  The inequalities are precisely what is
needed for the new tuple to remain ordered. -/
structure SingleVertexInsertion (S : PathTwoOpenSubdivision p U V) where
  segment : Fin (S.n + 1)
  parameter : unitInterval
  lower : S.vertex segment.castSucc ≤ parameter
  upper : parameter ≤ S.vertex segment.succ

end PathTwoOpenSubdivision

#print axioms PathTwoOpenSubdivision.insertedVertex_old
#print axioms PathTwoOpenSubdivision.insertedSide_old

end ConstructionTargets.FundamentalGroupoidTwoOpenInsertion
