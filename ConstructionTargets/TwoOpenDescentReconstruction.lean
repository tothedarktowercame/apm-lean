import ConstructionTargets.TwoOpenDescentFullness

/-!
# Object-level reconstruction for two-open descent

An ambient fundamental-groupoid functor restricts canonically to compatible
data on the two cover pieces.  This file constructs that datum and records the
object coordinates of its reconstruction.
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenDescentReconstruction

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.TwoOpenDescentRestriction
open ConstructionTargets.TwoOpenDescentFunctor

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- Mapping a path lifted to one cover piece back along the subtype inclusion
recovers its original ambient fundamental-groupoid morphism. -/
theorem map_pathInPiece_coverPieceInclusion
    (b : Bool) {x y : X} (p : Path x y)
    (hp : ∀ t, p t ∈ twoChart U V b) :
    (FundamentalGroupoid.map (coverPieceInclusion b)).map
        (FundamentalGroupoid.fromPath
          (Path.Homotopic.Quotient.mk (pathInPiece U V b p hp))) =
      FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p) := by
  change Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk (pathInPiece U V b p hp))
      (coverPieceInclusion b) = Path.Homotopic.Quotient.mk p
  rw [← Path.Homotopic.Quotient.mk_map]
  congr 1

/-- The canonical two-open descent datum obtained by restricting an ambient
functor along both subtype inclusions. -/
def canonicalTwoOpenDescentDatum (F : FundamentalGroupoid X ⥤ C) :
    @TwoOpenDescentDatum X _ U V C _ where
  obj x := F.obj ⟨x⟩
  functor b := FundamentalGroupoid.map (coverPieceInclusion b) ⋙ F
  obj_eq _ _ := rfl
  overlap_eq := by
    intro x y p hU hV
    simp only [Functor.comp_map]
    rw [map_pathInPiece_coverPieceInclusion false p
      (by simpa [twoChart] using hV)]
    rw [map_pathInPiece_coverPieceInclusion true p
      (by simpa [twoChart] using hU)]
    congr 1

@[simp] theorem canonicalTwoOpenDescentDatum_obj
    (F : FundamentalGroupoid X ⥤ C) (x : X) :
    (canonicalTwoOpenDescentDatum (U := U) (V := V) F).obj x = F.obj ⟨x⟩ := rfl

@[simp] theorem canonicalTwoOpenDescentDatum_functor
    (F : FundamentalGroupoid X ⥤ C) (b : Bool) :
    (canonicalTwoOpenDescentDatum (U := U) (V := V) F).functor b =
      FundamentalGroupoid.map (coverPieceInclusion b) ⋙ F := rfl

/-- Reconstruction has exactly the same object as the original ambient
functor.  This is kept as an isomorphism so it can be used as the component of
the eventual natural reconstruction isomorphism. -/
def canonicalReconstructionAppIso
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (F : FundamentalGroupoid X ⥤ C) (x : FundamentalGroupoid X) :
    (twoOpenDescentFunctor hU hV hcover
        (canonicalTwoOpenDescentDatum (U := U) (V := V) F)).obj x ≅ F.obj x :=
  Iso.refl _

@[simp] theorem canonicalReconstructionAppIso_hom
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (F : FundamentalGroupoid X ⥤ C) (x : FundamentalGroupoid X) :
    (canonicalReconstructionAppIso hU hV hcover F x).hom = 𝟙 (F.obj x) := rfl

/-- The already proved converse object-level comparison: arbitrary descent
data restricts back to each supplied piece functor up to its `obj_eq`
coordinates. -/
def descentPieceReconstructionIso
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) (b : Bool) :
    D.functor b ≅
      FundamentalGroupoid.map (coverPieceInclusion b) ⋙
        twoOpenDescentFunctor hU hV hcover D :=
  pieceRestrictionIso hU hV hcover D b

#print axioms map_pathInPiece_coverPieceInclusion
#print axioms canonicalTwoOpenDescentDatum
#print axioms canonicalReconstructionAppIso
#print axioms descentPieceReconstructionIso

end ConstructionTargets.TwoOpenDescentReconstruction
