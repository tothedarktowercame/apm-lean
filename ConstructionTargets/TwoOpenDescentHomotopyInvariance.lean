import ConstructionTargets.HomotopySquareTimeTelescope

/-!
# Representative-level homotopy invariance of two-open descent evaluation
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenDescentHomotopyInvariance

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.HomotopySquareUniformGrid
open ConstructionTargets.HomotopySquareRowSubdivisions
open ConstructionTargets.HomotopySquareTimeTelescope
open ConstructionTargets.PathSubdivisionEvaluationIndependence

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p q : Path x y} {U V : Set X}
variable {C : Type*} [Category C]

/-- Transport a subdivision certificate across equality of its underlying
path.  The endpoint types remain fixed. -/
def castSubdivision {r s : Path x y} (h : r = s)
    (S : PathTwoOpenSubdivision r U V) : PathTwoOpenSubdivision s U V :=
  h ▸ S

theorem evaluate_castSubdivision
    (D : @TwoOpenDescentDatum X _ U V C _)
    {r s : Path x y} (h : r = s) (S : PathTwoOpenSubdivision r U V) :
    D.evaluate (castSubdivision h S) = D.evaluate S := by
  subst s
  rfl

/-- With a fixed subordinate homotopy grid, arbitrary subdivisions of the
source and target paths have equal evaluation. -/
theorem evaluate_eq_of_homotopy_grid (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    D.evaluate S = D.evaluate T := by
  let S₀ : PathTwoOpenSubdivision p U V :=
    castSubdivision (firstStrip_rowPath H G)
      (bottomSubdivision H G (firstStrip H G))
  let T₁ : PathTwoOpenSubdivision q U V :=
    castSubdivision (lastStrip_rowPath H G)
      (topSubdivision H G (lastStrip H G))
  calc
    D.evaluate S = D.evaluate S₀ := evaluate_eq_of_subdivisions D S S₀
    _ = D.evaluate (bottomSubdivision H G (firstStrip H G)) :=
      evaluate_castSubdivision D (firstStrip_rowPath H G) _
    _ = D.evaluate (topSubdivision H G (lastStrip H G)) :=
      chosen_endpoint_evaluations_eq H G D
    _ = D.evaluate T₁ :=
      (evaluate_castSubdivision D (lastStrip_rowPath H G) _).symm
    _ = D.evaluate T := evaluate_eq_of_subdivisions D T₁ T

/-- Evaluation is invariant under a supplied endpoint-relative path homotopy,
for arbitrary subordinate subdivisions of its two endpoint paths. -/
theorem evaluate_eq_of_pathHomotopy
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (H : Path.Homotopy p q)
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    D.evaluate S = D.evaluate T := by
  let G := Classical.choice
    (exists_homotopySquareGrid H.toContinuousMap hU hV hcover)
  exact evaluate_eq_of_homotopy_grid H G D S T

/-- Representative-level form ready for quotient descent: a witness of
`Path.Homotopic` identifies evaluations of arbitrary subordinate
certificates. -/
theorem evaluate_eq_of_homotopic
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (h : Path.Homotopic p q)
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    D.evaluate S = D.evaluate T := by
  rcases h with ⟨H⟩
  exact evaluate_eq_of_pathHomotopy hU hV hcover H D S T

#print axioms evaluate_castSubdivision
#print axioms evaluate_eq_of_homotopy_grid
#print axioms evaluate_eq_of_pathHomotopy
#print axioms evaluate_eq_of_homotopic

end ConstructionTargets.TwoOpenDescentHomotopyInvariance
