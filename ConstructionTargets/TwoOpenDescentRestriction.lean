import ConstructionTargets.TwoOpenDescentFunctor
import ConstructionTargets.PathMapPathTransport

/-!
# Restriction of the two-open descent functor

The ambient descent functor restricts to each cover-piece functor through the
object-coordinate equalities carried by `TwoOpenDescentDatum`.
-/

open Set CategoryTheory
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.TwoOpenDescentRestriction

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.TwoOpenDescentFunctor
open ConstructionTargets.PathMapPathTransport

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- The continuous inclusion of a cover piece into the ambient space. -/
def coverPieceInclusion (b : Bool) : C(CoverPiece U V b, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The ambient path underlying a path in one cover piece. -/
def ambientPiecePath {b : Bool} {a z : CoverPiece U V b} (r : Path a z) :
    Path a.1 z.1 :=
  r.map continuous_subtype_val

@[simp] theorem ambientPiecePath_apply {b : Bool} {a z : CoverPiece U V b}
    (r : Path a z) (t : unitInterval) : ambientPiecePath r t = r t := rfl

theorem ambientPiecePath_mem {b : Bool} {a z : CoverPiece U V b}
    (r : Path a z) (t : unitInterval) :
    ambientPiecePath r t ∈ twoChart U V b := by
  simpa using (r t).2

theorem pathInPiece_ambientPiecePath {b : Bool} {a z : CoverPiece U V b}
    (r : Path a z) :
    pathInPiece U V b (ambientPiecePath r) (ambientPiecePath_mem r) = r := by
  apply Path.ext
  funext t
  rfl

/-- The one-segment ambient subdivision associated to a path already lying in
one member of the cover. -/
def onePieceSubdivision {b : Bool} {a z : CoverPiece U V b} (r : Path a z) :
    PathTwoOpenSubdivision (ambientPiecePath r) U V where
  n := 0
  vertex i := if i = 0 then 0 else 1
  side _ := b
  vertex_zero := by simp
  vertex_last := by simp
  monotone_vertex := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  segment_mem := by
    intro k t ht
    simpa using ambientPiecePath_mem r t

theorem onePieceSubdivision_point_zero {b : Bool} {a z : CoverPiece U V b}
    (r : Path a z) : (onePieceSubdivision r).point 0 = a.1 := by
  exact (onePieceSubdivision r).point_zero

theorem onePieceSubdivision_point_last {b : Bool} {a z : CoverPiece U V b}
    (r : Path a z) : (onePieceSubdivision r).point (Fin.last 1) = z.1 := by
  exact (onePieceSubdivision r).point_last

theorem onePieceSubdivision_piece {b : Bool} {a z : CoverPiece U V b}
    (r : Path a z) :
    (onePieceSubdivision r).piece 0 =
      (ambientPiecePath r).cast
        (onePieceSubdivision_point_zero r)
        (onePieceSubdivision_point_last r) := by
  apply Path.ext
  funext t
  change (ambientPiecePath r).subpath
      ((onePieceSubdivision r).vertex (Fin.castSucc 0))
      ((onePieceSubdivision r).vertex (Fin.succ 0)) t = _
  rw [show (onePieceSubdivision r).vertex (Fin.castSucc 0) = 0 by
    exact (onePieceSubdivision r).vertex_zero]
  rw [show (onePieceSubdivision r).vertex (Fin.succ 0) = 1 by
    exact (onePieceSubdivision r).vertex_last]
  rw [Path.subpath_zero_one]
  rfl

theorem composeFin_one (A : Fin 2 → C)
    (f : (k : Fin 1) → A k.castSucc ⟶ A k.succ) :
    TwoOpenDescentDatum.composeFin A f = f 0 := by
  rw [TwoOpenDescentDatum.composeFin_succ]
  simp

theorem mapPath_subpath_zero_one
    (D : @TwoOpenDescentDatum X _ U V C _)
    {b : Bool} {x y : X} (p : Path x y)
    (hp : ∀ t, p t ∈ twoChart U V b)
    (hp' : ∀ t, p.subpath 0 1 t ∈ twoChart U V b) :
    D.mapPath b (p.subpath 0 1) hp' =
      eqToHom (congrArg D.obj p.source) ≫ D.mapPath b p hp ≫
        eqToHom (congrArg D.obj p.target).symm := by
  simpa only [Path.subpath_zero_one] using
    PathMapPathTransport.TwoOpenDescentDatum.mapPath_cast
      D p p.source p.target hp (by simpa using hp')

theorem evaluate_onePieceSubdivision
    (D : @TwoOpenDescentDatum X _ U V C _)
    {b : Bool} {a z : CoverPiece U V b} (r : Path a z) :
    D.evaluate (onePieceSubdivision r) =
      D.mapPath b (ambientPiecePath r) (ambientPiecePath_mem r) := by
  unfold TwoOpenDescentDatum.evaluate
  dsimp only [onePieceSubdivision]
  rw [composeFin_one]
  unfold TwoOpenDescentDatum.mappedPiece
  change eqToHom _ ≫
      D.mapPath b ((ambientPiecePath r).subpath 0 1) _ ≫ eqToHom _ = _
  rw [mapPath_subpath_zero_one D (ambientPiecePath r) (ambientPiecePath_mem r)]
  simp only [Category.assoc]
  simp

theorem mapPath_ambientPiecePath
    (D : @TwoOpenDescentDatum X _ U V C _)
    {b : Bool} {a z : CoverPiece U V b} (r : Path a z) :
    D.mapPath b (ambientPiecePath r) (ambientPiecePath_mem r) =
      eqToHom (D.obj_eq b ⟨a⟩).symm ≫
        (D.functor b).map (Path.Homotopic.Quotient.mk r) ≫
        eqToHom (D.obj_eq b ⟨z⟩) := by
  unfold TwoOpenDescentDatum.mapPath
  rw [pathInPiece_ambientPiecePath]

/-- The ambient descent functor, restricted along the subtype inclusion. -/
def restrictedAmbientFunctor (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) (b : Bool) :
    FundamentalGroupoid (CoverPiece U V b) ⥤ C :=
  FundamentalGroupoid.map (coverPieceInclusion b) ⋙
    twoOpenDescentFunctor hU hV hcover D

/-- The object-coordinate comparison between the original piece functor and
the restriction of the ambient descent functor. -/
def restrictionAppIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) (b : Bool)
    (z : FundamentalGroupoid (CoverPiece U V b)) :
    (D.functor b).obj z ≅ (restrictedAmbientFunctor hU hV hcover D b).obj z :=
  eqToIso (D.obj_eq b z)

theorem restrictedAmbientFunctor_map_mk
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _)
    {b : Bool} {a z : CoverPiece U V b} (r : Path a z) :
    (restrictedAmbientFunctor hU hV hcover D b).map
        (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk r)) =
      D.evaluate (onePieceSubdivision r) := by
  change (twoOpenDescentFunctor hU hV hcover D).map
      (FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk (ambientPiecePath r))) = _
  exact twoOpenDescentFunctor_map_mk hU hV hcover D _ _

/-- Restricting the ambient descent functor to either cover piece recovers the
supplied piece functor, up to its explicit object-coordinate transports. -/
def pieceRestrictionIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) (b : Bool) :
    D.functor b ≅ restrictedAmbientFunctor hU hV hcover D b :=
  NatIso.ofComponents (restrictionAppIso hU hV hcover D b) (by
    rintro ⟨a⟩ ⟨z⟩ ⟨r⟩
    change (D.functor b).map (Path.Homotopic.Quotient.mk r) ≫
        (restrictionAppIso hU hV hcover D b ⟨z⟩).hom =
      (restrictionAppIso hU hV hcover D b ⟨a⟩).hom ≫
        (restrictedAmbientFunctor hU hV hcover D b).map
          (Path.Homotopic.Quotient.mk r)
    rw [restrictedAmbientFunctor_map_mk hU hV hcover D r]
    rw [evaluate_onePieceSubdivision D r]
    rw [mapPath_ambientPiecePath]
    change (D.functor b).map (Path.Homotopic.Quotient.mk r) ≫
        (eqToIso (D.obj_eq b ⟨z⟩)).hom =
      (eqToIso (D.obj_eq b ⟨a⟩)).hom ≫
        ((eqToIso (D.obj_eq b ⟨a⟩)).inv ≫
          (D.functor b).map (Path.Homotopic.Quotient.mk r) ≫
          (eqToIso (D.obj_eq b ⟨z⟩)).hom)
    simp)

#print axioms onePieceSubdivision
#print axioms evaluate_onePieceSubdivision
#print axioms restrictedAmbientFunctor_map_mk
#print axioms pieceRestrictionIso

end ConstructionTargets.TwoOpenDescentRestriction
