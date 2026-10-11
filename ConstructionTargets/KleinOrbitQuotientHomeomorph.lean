import ConstructionTargets.KleinClosedSquareOrbitQuotientEquiv
import ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace ConstructionTargets.KleinOrbitQuotientHomeomorph

open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.KleinClosedSquareOrbitQuotientEquiv

abbrev PlaneOrbitQuotient := Quotient orbitSetoid
abbrev ClosedSquareOrbitQuotient := Quotient closedSquareOrbitSetoid

noncomputable instance : TopologicalSpace PlaneOrbitQuotient :=
  TopologicalSpace.coinduced
    (fun p : ℝ × ℝ => Quotient.mk orbitSetoid p) inferInstance

noncomputable instance : TopologicalSpace ClosedSquareOrbitQuotient :=
  TopologicalSpace.coinduced
    (fun p : ClosedSquare => Quotient.mk closedSquareOrbitSetoid p) inferInstance

/-- The set-theoretic fundamental-domain equivalence has a continuous forward
map for the actual quotient topologies.  This is the direction that follows
formally from the quotient universal property. -/
theorem continuous_closedSquareToOrbitQuotient :
    Continuous closedSquareToOrbitQuotient := by
  apply Continuous.quotient_lift
  exact continuous_coinduced_rng.comp continuous_subtype_val

theorem continuous_closedSquareOrbitQuotientEquiv :
    Continuous (closedSquareOrbitQuotientEquiv :
      ClosedSquareOrbitQuotient → PlaneOrbitQuotient) :=
  continuous_closedSquareToOrbitQuotient

#print axioms continuous_closedSquareOrbitQuotientEquiv

end ConstructionTargets.KleinOrbitQuotientHomeomorph
