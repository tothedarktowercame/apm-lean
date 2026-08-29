import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom

/-!
# Round-trip coherence for a span transported by equivalences

This file isolates the categorical triangle used when a span leg is moved to
equivalent source and target categories and then moved back.  The comparison
retains the equality transport witnessing the coordinate description of the
leg.
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.EquivalenceSpanRoundTrip

universe uO uO' uP uP' uC

variable {O : Type uO} {O' : Type uO'} {P : Type uP} {P' : Type uP'}
  {C : Type uC}
  [Category O] [Category O'] [Category P] [Category P'] [Category C]

/-- Forward comparison for a span leg written in equivalent coordinates. -/
def forwardSpanComparison
    (eO : O ≌ O') (eP : P ≌ P') (J : Functor O P) (K : Functor O' P')
    (q : eO.inverse ⋙ J ⋙ eP.functor = K) (L : Functor P C) :
    K ⋙ eP.inverse ⋙ L ≅ eO.inverse ⋙ J ⋙ L := by
  let q' : K ⋙ eP.inverse =
      eO.inverse ⋙ J ⋙ eP.functor ⋙ eP.inverse :=
    congrArg (fun A => A ⋙ eP.inverse) q.symm
  exact (Functor.isoWhiskerRight (eqToIso q') L).trans
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (eO.inverse ⋙ J) eP.unitIso.symm) L)

/-- Reverse comparison for the same span leg. -/
def reverseSpanComparison
    (eO : O ≌ O') (eP : P ≌ P') (J : Functor O P) (K : Functor O' P')
    (q : eO.inverse ⋙ J ⋙ eP.functor = K) (L : Functor P' C) :
    eO.functor ⋙ K ⋙ L ≅ J ⋙ eP.functor ⋙ L := by
  let q' : eO.functor ⋙ K =
      eO.functor ⋙ eO.inverse ⋙ J ⋙ eP.functor :=
    congrArg (fun A => eO.functor ⋙ A) q.symm
  exact (Functor.isoWhiskerRight (eqToIso q') L).trans
    (Functor.isoWhiskerRight (eO.funInvIdAssoc (J ⋙ eP.functor)) L)

/-- Moving a span forward and back cancels to the inverse unit on its target
piece.  The overlap unit is retained as `funInvIdAssoc`; no functor equality is
treated as definitional. -/
theorem spanRoundTrip_triangle
    (eO : O ≌ O') (eP : P ≌ P') (J : Functor O P) (K : Functor O' P')
    (q : eO.inverse ⋙ J ⋙ eP.functor = K) (L : Functor P C) :
    (reverseSpanComparison eO eP J K q (eP.inverse ⋙ L)).inv ≫
        Functor.whiskerLeft eO.functor
          (forwardSpanComparison eO eP J K q L).hom ≫
        (eO.funInvIdAssoc (J ⋙ L)).hom =
      Functor.whiskerLeft J (eP.congrLeft.unitIso.inv.app L) := by
  subst K
  ext X
  simp [forwardSpanComparison, reverseSpanComparison, Category.assoc]
  simp only [← L.map_comp]
  simp
  rw [← L.map_comp, ← J.map_comp]
  have hu : eO.unit.app X ≫ eO.unitInv.app X = 𝟙 X := by
    simpa using eO.unitIso.hom_inv_id_app X
  have hj : J.map (eO.unit.app X ≫ eO.unitInv.app X) = 𝟙 (J.obj X) := by
    calc
      _ = J.map (𝟙 X) := congrArg J.map hu
      _ = _ := by simpa using J.map_id X
  have hl : L.map (J.map (eO.unit.app X ≫ eO.unitInv.app X)) =
      𝟙 (L.obj (J.obj X)) := by
    calc
      _ = L.map (𝟙 (J.obj X)) := congrArg L.map hj
      _ = _ := by simpa using L.map_id (J.obj X)
  calc
    _ = L.map (eP.unitInv.app (J.obj X)) ≫ 𝟙 _ :=
      congrArg (fun t => L.map (eP.unitInv.app (J.obj X)) ≫ t) hl
    _ = _ := Category.comp_id _

/-- Inverse orientation of `spanRoundTrip_triangle`.  This is the form used on
the outgoing leg of a transported glue square. -/
theorem spanRoundTrip_triangle_inv
    (eO : O ≌ O') (eP : P ≌ P') (J : Functor O P) (K : Functor O' P')
    (q : eO.inverse ⋙ J ⋙ eP.functor = K) (L : Functor P C) :
    (eO.funInvIdAssoc (J ⋙ L)).inv ≫
        Functor.whiskerLeft eO.functor
          (forwardSpanComparison eO eP J K q L).inv ≫
        (reverseSpanComparison eO eP J K q (eP.inverse ⋙ L)).hom =
      Functor.whiskerLeft J ((eP.congrLeft).unitIso.hom.app L) := by
  let a := (reverseSpanComparison eO eP J K q (eP.inverse ⋙ L)).symm |>.trans
    ((Functor.isoWhiskerLeft eO.functor
      (forwardSpanComparison eO eP J K q L)).trans
        (eO.funInvIdAssoc (J ⋙ L)))
  let b := Functor.isoWhiskerLeft J ((eP.congrLeft).unitIso.app L).symm
  have hab : a = b := Iso.ext (spanRoundTrip_triangle eO eP J K q L)
  simpa [a, b, Category.assoc] using congrArg Iso.inv hab

#print axioms forwardSpanComparison
#print axioms reverseSpanComparison
#print axioms spanRoundTrip_triangle
#print axioms spanRoundTrip_triangle_inv

end ConstructionTargets.EquivalenceSpanRoundTrip
