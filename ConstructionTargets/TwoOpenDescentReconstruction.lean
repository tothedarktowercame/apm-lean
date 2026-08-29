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
open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.TwoOpenDescentRestriction
open ConstructionTargets.TwoOpenDescentFunctor
open ConstructionTargets.TwoOpenDescentQuotient

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- A functor maps a finite concatenation of paths to the corresponding
`composeFin` of the mapped path classes. -/
theorem map_pathConcat_eq_composeFin (F : FundamentalGroupoid X ⥤ C)
    {n : ℕ} (point : Fin (n + 1) → X)
    (piece : (k : Fin n) → Path (point k.castSucc) (point k.succ)) :
    F.map (FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk (Path.concat point piece))) =
      TwoOpenDescentDatum.composeFin (F.obj ∘ fun i ↦ ⟨point i⟩)
        (fun k ↦ F.map (FundamentalGroupoid.fromPath
          (Path.Homotopic.Quotient.mk (piece k)))) := by
  induction n with
  | zero =>
      rw [Path.concat_zero]
      change F.map (𝟙 ⟨point 0⟩) = _
      simp
  | succ n ih =>
      rw [Path.concat_succ]
      change F.map (Path.Homotopic.Quotient.mk
        ((Path.concat (point ∘ Fin.castSucc) (fun k ↦ piece k.castSucc)).trans
          (piece (Fin.last n)))) = _
      change F.map (Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk
          (Path.concat (point ∘ Fin.castSucc) (fun k ↦ piece k.castSucc)))
        (Path.Homotopic.Quotient.mk (piece (Fin.last n)))) = _
      change F.map (_ ≫ _) = _
      rw [F.map_comp, TwoOpenDescentDatum.composeFin_succ]
      have hprefix := ih (point ∘ Fin.castSucc) (fun k ↦ piece k.castSucc)
      exact congrArg
        (fun q ↦ q ≫ F.map (Path.Homotopic.Quotient.mk (piece (Fin.last n))))
        hprefix

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

/-- Each canonical mapped subdivision piece is literally the original functor
applied to its ambient path class. -/
theorem canonical_mappedPiece
    (F : FundamentalGroupoid X ⥤ C) {x y : X} {p : Path x y}
    (S : PathTwoOpenSubdivision p U V) (k : Fin (S.n + 1)) :
    (canonicalTwoOpenDescentDatum (U := U) (V := V) F).mappedPiece S k =
      F.map (FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk (S.piece k))) := by
  unfold TwoOpenDescentDatum.mappedPiece TwoOpenDescentDatum.mapPath
  simp only [canonicalTwoOpenDescentDatum, Functor.comp_map]
  rw [map_pathInPiece_coverPieceInclusion]
  change (𝟙 _) ≫ F.map (FundamentalGroupoid.fromPath
      (Path.Homotopic.Quotient.mk (S.piece k))) ≫ (𝟙 _) = _
  simp

theorem canonical_composeFin
    (F : FundamentalGroupoid X ⥤ C) {x y : X} {p : Path x y}
    (S : PathTwoOpenSubdivision p U V) :
    TwoOpenDescentDatum.composeFin
        ((canonicalTwoOpenDescentDatum (U := U) (V := V) F).obj ∘ S.point)
        ((canonicalTwoOpenDescentDatum (U := U) (V := V) F).mappedPiece S) =
      F.map (FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk (Path.concat S.point S.piece))) := by
  rw [map_pathConcat_eq_composeFin]
  apply congrArg
  funext k
  exact canonical_mappedPiece F S k

/-- Removing the endpoint casts from a cast path class. -/
theorem fromPath_cast_unbracket {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) :
    eqToHom (congrArg FundamentalGroupoid.mk hx).symm ≫
        FundamentalGroupoid.fromPath
          (Path.Homotopic.Quotient.mk (p.cast hx hy)) ≫
        eqToHom (congrArg FundamentalGroupoid.mk hy) =
      FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p) := by
  rw [← FundamentalGroupoid.conj_eqToHom hx hy]
  simp

theorem map_fromPath_cast_unbracket (F : FundamentalGroupoid X ⥤ C)
    {x y x' y' : X} (p : Path x y) (hx : x' = x) (hy : y' = y) :
    eqToHom (congrArg (fun z : X ↦ F.obj ⟨z⟩) hx).symm ≫
        F.map (FundamentalGroupoid.fromPath
          (Path.Homotopic.Quotient.mk (p.cast hx hy))) ≫
        eqToHom (congrArg (fun z : X ↦ F.obj ⟨z⟩) hy) =
      F.map (FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk p)) := by
  subst x'
  subst y'
  simp

/-- Evaluation of any subordinate subdivision for the canonical datum
reconstructs the original ambient functor map. -/
theorem canonical_evaluate
    (F : FundamentalGroupoid X ⥤ C) {x y : X} (p : Path x y)
    (S : PathTwoOpenSubdivision p U V) :
    (canonicalTwoOpenDescentDatum (U := U) (V := V) F).evaluate S =
      F.map (FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk p)) := by
  unfold TwoOpenDescentDatum.evaluate
  rw [canonical_composeFin F S]
  rw [S.quotient_concat_eq]
  change eqToHom _ ≫ F.map (FundamentalGroupoid.fromPath
      (Path.Homotopic.Quotient.mk (p.cast S.point_zero S.point_last))) ≫
      eqToHom _ = _
  exact map_fromPath_cast_unbracket F p S.point_zero S.point_last

/-- Reconstruction has exactly the same object as the original ambient
functor.  This is kept as an isomorphism so it can be used as the component of
the eventual natural reconstruction isomorphism. -/
def canonicalReconstructionAppIso
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (F : FundamentalGroupoid X ⥤ C) (x : FundamentalGroupoid X) :
    (twoOpenDescentFunctor hU hV hcover
        (canonicalTwoOpenDescentDatum (U := U) (V := V) F)).obj x ≅ F.obj x :=
  Iso.refl _

/-- Restricting an ambient functor and descending again recovers it by the
identity object components and the proved morphism reconstruction formula. -/
def canonicalReconstructionIso
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (F : FundamentalGroupoid X ⥤ C) :
    twoOpenDescentFunctor hU hV hcover
        (canonicalTwoOpenDescentDatum (U := U) (V := V) F) ≅ F :=
  NatIso.ofComponents (canonicalReconstructionAppIso hU hV hcover F) (by
    rintro ⟨x⟩ ⟨y⟩ ⟨p⟩
    change (twoOpenDescentFunctor hU hV hcover
        (canonicalTwoOpenDescentDatum (U := U) (V := V) F)).map
          (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p)) ≫
          𝟙 _ =
      𝟙 _ ≫ F.map
        (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p))
    simp only [Category.comp_id, Category.id_comp]
    rw [twoOpenDescentFunctor_map_mk hU hV hcover _ p
      (chosenSubdivision hU hV hcover p)]
    exact canonical_evaluate F p (chosenSubdivision hU hV hcover p))

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
#print axioms map_pathConcat_eq_composeFin
#print axioms canonical_mappedPiece
#print axioms canonical_composeFin
#print axioms canonical_evaluate
#print axioms canonicalReconstructionAppIso
#print axioms canonicalReconstructionIso
#print axioms descentPieceReconstructionIso

end ConstructionTargets.TwoOpenDescentReconstruction
