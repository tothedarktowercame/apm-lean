import ConstructionTargets.HomotopySquareStripEvaluation
import ConstructionTargets.PathSubdivisionEvaluationIndependence

/-!
# Telescoping two-open descent evaluation across a homotopy grid
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.HomotopySquareTimeTelescope

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.HomotopySquareUniformGrid
open ConstructionTargets.HomotopySquareRowSubdivisions
open ConstructionTargets.HomotopySquareStripEvaluation
open ConstructionTargets.PathSubdivisionEvaluationIndependence

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p q : Path x y} {U V : Set X}
variable {C : Type*} [Category C]

def firstStrip (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) : Fin G.N :=
  Fin.cast (rowSubdivisionN_add_one G) 0

def lastStrip (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) : Fin G.N :=
  Fin.cast (rowSubdivisionN_add_one G) (Fin.last (rowSubdivisionN G))

@[simp] theorem firstStrip_rowPath (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) :
    rowPath H G (firstStrip H G).castSucc = p := by
  have hz : (firstStrip H G).castSucc = (0 : Fin (G.N + 1)) := by
    apply Fin.ext
    rfl
  rw [hz, rowPath_zero]

@[simp] theorem lastStrip_rowPath (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) :
    rowPath H G (lastStrip H G).succ = q := by
  have hl : (lastStrip H G).succ = Fin.last G.N := by
    apply Fin.ext
    change rowSubdivisionN G + 1 = G.N
    exact rowSubdivisionN_add_one G
  rw [hl, rowPath_last]

/-- Consecutive strips assign the same evaluation to their shared horizontal
row, even though their subordinate certificates may use different labels. -/
theorem adjacent_strip_evaluate_compatible (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _)
    (i : Fin (rowSubdivisionN G)) :
    D.evaluate (topSubdivision H G
        (Fin.cast (rowSubdivisionN_add_one G) i.castSucc)) =
      D.evaluate (bottomSubdivision H G
        (Fin.cast (rowSubdivisionN_add_one G) i.succ)) := by
  let il : Fin G.N := Fin.cast (rowSubdivisionN_add_one G) i.castSucc
  let ir : Fin G.N := Fin.cast (rowSubdivisionN_add_one G) i.succ
  have hi : il.succ = ir.castSucc := by
    apply Fin.ext
    rfl
  cases hi
  exact evaluate_eq_of_subdivisions D _ _

/-- Every bottom-row evaluation agrees with the bottom row of the first time
strip. -/
theorem first_bottom_evaluate_eq_bottom (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _)
    (i : Fin (rowSubdivisionN G + 1)) :
    D.evaluate (bottomSubdivision H G (firstStrip H G)) =
      D.evaluate (bottomSubdivision H G
        (Fin.cast (rowSubdivisionN_add_one G) i)) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih =>
      calc
        D.evaluate (bottomSubdivision H G (firstStrip H G)) =
            D.evaluate (bottomSubdivision H G
              (Fin.cast (rowSubdivisionN_add_one G) j.castSucc)) := ih
        _ = D.evaluate (topSubdivision H G
              (Fin.cast (rowSubdivisionN_add_one G) j.castSucc)) :=
          bottom_evaluate_eq_top H G D _
        _ = D.evaluate (bottomSubdivision H G
              (Fin.cast (rowSubdivisionN_add_one G) j.succ)) :=
          adjacent_strip_evaluate_compatible H G D j

/-- The selected subdivisions on the source row and target row of the grid
have equal descent evaluation.  Their underlying paths reduce to `p` and `q`
by `rowPath_zero` and `rowPath_last`. -/
theorem chosen_endpoint_evaluations_eq (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) :
    D.evaluate (bottomSubdivision H G (firstStrip H G)) =
      D.evaluate (topSubdivision H G (lastStrip H G)) := by
  calc
    D.evaluate (bottomSubdivision H G (firstStrip H G)) =
        D.evaluate (bottomSubdivision H G
          (Fin.cast (rowSubdivisionN_add_one G)
            (Fin.last (rowSubdivisionN G)))) :=
      first_bottom_evaluate_eq_bottom H G D _
    _ = D.evaluate (topSubdivision H G
          (Fin.cast (rowSubdivisionN_add_one G)
            (Fin.last (rowSubdivisionN G)))) :=
      bottom_evaluate_eq_top H G D _
    _ = D.evaluate (topSubdivision H G (lastStrip H G)) := rfl

#print axioms adjacent_strip_evaluate_compatible
#print axioms firstStrip_rowPath
#print axioms lastStrip_rowPath
#print axioms first_bottom_evaluate_eq_bottom
#print axioms chosen_endpoint_evaluations_eq

end ConstructionTargets.HomotopySquareTimeTelescope
