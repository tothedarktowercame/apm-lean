import ConstructionTargets.HomotopySquareStripEndpoints

/-!
# Evaluation equality across one homotopy-grid strip
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.HomotopySquareStripEvaluation

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.HomotopySquareUniformGrid
open ConstructionTargets.HomotopySquareRowSubdivisions
open ConstructionTargets.HomotopySquareStripLadder
open ConstructionTargets.HomotopySquareStripEndpoints

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p q : Path x y} {U V : Set X}
variable {C : Type*} [Category C]

theorem eqToHom_reverse_cancel {A B : C} (h : A = B) (h' : B = A) :
    eqToHom h ≫ eqToHom h' = 𝟙 A := by
  subst B
  simp

/-- The normalized initial vertical converts the bottom evaluation prefix to
the top evaluation prefix. -/
theorem initial_stripVertical_prefix (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N) :
    eqToHom (congrArg D.obj (bottomSubdivision H G i).point_zero).symm ≫
        stripVertical H G D i 0 =
      eqToHom (congrArg D.obj (topSubdivision H G i).point_zero).symm := by
  let back :=
    eqToHom (congrArg D.obj (topSubdivision H G i).point_zero.symm).symm
  apply (cancel_mono back).1
  calc
    (eqToHom (congrArg D.obj (bottomSubdivision H G i).point_zero).symm ≫
        stripVertical H G D i 0) ≫ back =
      eqToHom (congrArg D.obj (bottomSubdivision H G i).point_zero).symm ≫
        stripVertical H G D i 0 ≫ back := Category.assoc _ _ _
    _ = 𝟙 (D.obj x) := initial_stripVertical_normalized H G D i
    _ = eqToHom (congrArg D.obj (topSubdivision H G i).point_zero).symm ≫
        back := (eqToHom_reverse_cancel _ _).symm

/-- The normalized terminal vertical converts the top evaluation suffix to
the bottom evaluation suffix. -/
theorem terminal_stripVertical_suffix (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N) :
    stripVertical H G D i (Fin.last (rowSubdivisionN G + 1)) ≫
        eqToHom (congrArg D.obj (topSubdivision H G i).point_last) =
      eqToHom (congrArg D.obj (bottomSubdivision H G i).point_last) := by
  let front :=
    eqToHom (congrArg D.obj (bottomSubdivision H G i).point_last.symm)
  apply (cancel_epi front).1
  calc
    front ≫ (stripVertical H G D i (Fin.last (rowSubdivisionN G + 1)) ≫
        eqToHom (congrArg D.obj (topSubdivision H G i).point_last)) =
      𝟙 (D.obj y) := terminal_stripVertical_normalized H G D i
    _ = front ≫ eqToHom
        (congrArg D.obj (bottomSubdivision H G i).point_last) :=
      (eqToHom_reverse_cancel _ _).symm

/-- Evaluating the bottom and top row subdivisions of one fixed grid strip
gives the same common-coordinate morphism. -/
theorem bottom_evaluate_eq_top (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N) :
    D.evaluate (bottomSubdivision H G i) =
      D.evaluate (topSubdivision H G i) := by
  let pb := eqToHom
    (congrArg D.obj (bottomSubdivision H G i).point_zero).symm
  let pt := eqToHom
    (congrArg D.obj (topSubdivision H G i).point_zero).symm
  let sb := eqToHom
    (congrArg D.obj (bottomSubdivision H G i).point_last)
  let st := eqToHom
    (congrArg D.obj (topSubdivision H G i).point_last)
  let cb := TwoOpenDescentDatum.composeFin
    (D.obj ∘ (bottomSubdivision H G i).point)
    (D.mappedPiece (bottomSubdivision H G i))
  let ct := TwoOpenDescentDatum.composeFin
    (D.obj ∘ (topSubdivision H G i).point)
    (D.mappedPiece (topSubdivision H G i))
  let v0 := stripVertical H G D i 0
  let vl := stripVertical H G D i (Fin.last (rowSubdivisionN G + 1))
  have hfirst : pb ≫ v0 = pt := initial_stripVertical_prefix H G D i
  have hlast : vl ≫ st = sb := terminal_stripVertical_suffix H G D i
  have hstrip : cb ≫ vl = v0 ≫ ct := strip_composeFin_square H G D i
  have hcalc : (pb ≫ cb) ≫ sb = (pt ≫ ct) ≫ st := by calc
    (pb ≫ cb) ≫ sb = (pb ≫ cb) ≫ (vl ≫ st) :=
      congrArg (fun z ↦ (pb ≫ cb) ≫ z) hlast.symm
    _ = pb ≫ (cb ≫ vl) ≫ st := by simp only [Category.assoc]
    _ = pb ≫ (v0 ≫ ct) ≫ st :=
      congrArg (fun z ↦ pb ≫ z ≫ st) hstrip
    _ = (pb ≫ v0) ≫ ct ≫ st := by simp only [Category.assoc]
    _ = (pt ≫ ct) ≫ st := by
      rw [hfirst]
      exact (Category.assoc _ _ _).symm
  simpa only [TwoOpenDescentDatum.evaluate, pb, pt, sb, st, cb, ct,
    Category.assoc] using hcalc

#print axioms initial_stripVertical_prefix
#print axioms terminal_stripVertical_suffix
#print axioms bottom_evaluate_eq_top

end ConstructionTargets.HomotopySquareStripEvaluation
