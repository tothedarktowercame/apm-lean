import ConstructionTargets.KleinOrbitQuotientHomeomorph
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

namespace ConstructionTargets.KleinClosedSquareOrbitInverseContinuity

open Set
open KleinPlaneActionSquareOrbitClassification
open KleinClosedSquareOrbitQuotientEquiv
open KleinOrbitQuotientHomeomorph

theorem isCompact_closedSquare_set :
    IsCompact {p : ℝ × ℝ | InSquare p} := by
  have h : {p : ℝ × ℝ | InSquare p} =
      Set.Icc ((0, 0) : ℝ × ℝ) ((1, 1) : ℝ × ℝ) := by
    ext p
    constructor
    · rintro ⟨hx0, hx1, hy0, hy1⟩
      exact ⟨⟨hx0, hy0⟩, hx1, hy1⟩
    · rintro ⟨⟨hx0, hy0⟩, hx1, hy1⟩
      exact ⟨hx0, hx1, hy0, hy1⟩
  rw [h]
  exact isCompact_Icc

noncomputable instance closedSquare_compactSpace : CompactSpace ClosedSquare :=
  isCompact_iff_compactSpace.mp isCompact_closedSquare_set

noncomputable instance closedSquareOrbitQuotient_compactSpace :
    CompactSpace ClosedSquareOrbitQuotient :=
  Quotient.compactSpace

/-- Once the plane orbit quotient is known Hausdorff, the already compiled
continuous bijection from the compact fundamental-square quotient has a
continuous inverse. -/
theorem closedSquareOrbitQuotientEquiv_continuous_symm_of_t2
    [T2Space PlaneOrbitQuotient] :
    Continuous (closedSquareOrbitQuotientEquiv.symm :
      PlaneOrbitQuotient → ClosedSquareOrbitQuotient) :=
  continuous_closedSquareOrbitQuotientEquiv.continuous_symm_of_equiv_compact_to_t2

#print axioms isCompact_closedSquare_set
#print axioms closedSquareOrbitQuotientEquiv_continuous_symm_of_t2

end ConstructionTargets.KleinClosedSquareOrbitInverseContinuity
