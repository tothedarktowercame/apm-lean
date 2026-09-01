import Mathlib.CategoryTheory.Equivalence

/-!
# Round-trip coherence for a span transported by equivalences

This file isolates the categorical triangle used when a span leg is moved to
equivalent source and target categories and then moved back. The comparison
retains the supplied natural isomorphism witnessing the coordinate description
of the leg.
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
    (α : eO.inverse ⋙ J ⋙ eP.functor ≅ K) (L : Functor P C) :
    K ⋙ eP.inverse ⋙ L ≅ eO.inverse ⋙ J ⋙ L :=
  (Functor.isoWhiskerRight α.symm (eP.inverse ⋙ L)).trans
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (eO.inverse ⋙ J) eP.unitIso.symm) L)

/-- Reverse comparison for the same span leg. -/
def reverseSpanComparison
    (eO : O ≌ O') (eP : P ≌ P') (J : Functor O P) (K : Functor O' P')
    (α : eO.inverse ⋙ J ⋙ eP.functor ≅ K) (L : Functor P' C) :
    eO.functor ⋙ K ⋙ L ≅ J ⋙ eP.functor ⋙ L :=
  (Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft eO.functor α.symm) L).trans
    (Functor.isoWhiskerRight (eO.funInvIdAssoc (J ⋙ eP.functor)) L)

/-- Forward then reverse cancels an arbitrary span comparison iso. -/
theorem spanRoundTripIso_unit
    (eO : O ≌ O') (eP : P ≌ P') (J : Functor O P) (K : Functor O' P')
    (α : eO.inverse ⋙ J ⋙ eP.functor ≅ K) (L : Functor P C) :
    (reverseSpanComparison eO eP J K α (eP.inverse ⋙ L)).inv ≫
        Functor.whiskerLeft eO.functor
          (forwardSpanComparison eO eP J K α L).hom ≫
        (eO.funInvIdAssoc (J ⋙ L)).hom =
      Functor.whiskerLeft J ((eP.congrLeft).unitIso.inv.app L) := by
  ext X
  simp [forwardSpanComparison, reverseSpanComparison, Category.assoc]
  slice_lhs 4 5 =>
    exact calc
      _ = L.map (eP.inverse.map (α.hom.app (eO.functor.obj X)) ≫
          eP.inverse.map (α.inv.app (eO.functor.obj X))) :=
        (L.map_comp _ _).symm
      _ = L.map (eP.inverse.map (α.hom.app (eO.functor.obj X) ≫
          α.inv.app (eO.functor.obj X))) :=
        congrArg L.map (eP.inverse.map_comp _ _).symm
      _ = L.map (eP.inverse.map (𝟙 _)) :=
        congrArg (fun q => L.map (eP.inverse.map q))
          (α.hom_inv_id_app (eO.functor.obj X))
      _ = 𝟙 _ := by rw [eP.inverse.map_id, L.map_id]
  have hL : L.map (eP.unit.app (J.obj (eO.inverse.obj (eO.functor.obj X)))) ≫
      L.map (eP.unitIso.inv.app (J.obj (eO.inverse.obj (eO.functor.obj X)))) = 𝟙 _ := by
    rw [← L.map_comp]
    simp
  have hLassoc : L.map (eP.unit.app (J.obj (eO.inverse.obj (eO.functor.obj X)))) ≫
      L.map (eP.unitIso.inv.app (J.obj (eO.inverse.obj (eO.functor.obj X)))) ≫
      L.map (J.map (eO.unitInv.app X)) = L.map (J.map (eO.unitInv.app X)) := by
    rw [← Category.assoc, hL, Category.id_comp]
    rfl
  have hLassoc2 : L.map (eP.unit.app (J.obj (eO.inverse.obj (eO.functor.obj X)))) ≫
      𝟙 _ ≫ L.map (eP.unitIso.inv.app (J.obj (eO.inverse.obj (eO.functor.obj X)))) ≫
      L.map (J.map (eO.unitInv.app X)) = L.map (J.map (eO.unitInv.app X)) := by
    rw [Category.id_comp]
    exact hLassoc
  slice_lhs 3 6 => exact (by exact hLassoc2)
  have hu : eO.unit.app X ≫ eO.unitInv.app X = 𝟙 X := by
    simp
  slice_lhs 2 3 => exact calc
    _ = L.map (J.map (eO.unit.app X) ≫ J.map (eO.unitInv.app X)) :=
      (L.map_comp _ _).symm
    _ = L.map (J.map (eO.unit.app X ≫ eO.unitInv.app X)) :=
      congrArg L.map (J.map_comp _ _).symm
    _ = 𝟙 _ := by simp
  simp

/-- Inverse orientation of `spanRoundTripIso_unit`. -/
theorem spanRoundTripIso_unit_inv
    (eO : O ≌ O') (eP : P ≌ P') (J : Functor O P) (K : Functor O' P')
    (α : eO.inverse ⋙ J ⋙ eP.functor ≅ K) (L : Functor P C) :
    (eO.funInvIdAssoc (J ⋙ L)).inv ≫
        Functor.whiskerLeft eO.functor
          (forwardSpanComparison eO eP J K α L).inv ≫
        (reverseSpanComparison eO eP J K α (eP.inverse ⋙ L)).hom =
      Functor.whiskerLeft J ((eP.congrLeft).unitIso.hom.app L) := by
  let a := (reverseSpanComparison eO eP J K α (eP.inverse ⋙ L)).symm |>.trans
    ((Functor.isoWhiskerLeft eO.functor
      (forwardSpanComparison eO eP J K α L)).trans
        (eO.funInvIdAssoc (J ⋙ L)))
  let b := Functor.isoWhiskerLeft J ((eP.congrLeft).unitIso.app L).symm
  have hab : a = b := Iso.ext (spanRoundTripIso_unit eO eP J K α L)
  simpa [a, b, Category.assoc] using congrArg Iso.inv hab

/-- Reverse then forward cancels an arbitrary span comparison iso. -/
theorem spanRoundTripIso_counit
    (eO : O ≌ O') (eP : P ≌ P') (J : Functor O P) (K : Functor O' P')
    (α : eO.inverse ⋙ J ⋙ eP.functor ≅ K) (L : Functor P' C) :
    (forwardSpanComparison eO eP J K α (eP.functor ⋙ L)).hom ≫
        Functor.whiskerLeft eO.inverse
          (reverseSpanComparison eO eP J K α L).inv ≫
        (eO.invFunIdAssoc (K ⋙ L)).hom =
      Functor.whiskerLeft K ((eP.congrLeft).counitIso.hom.app L) := by
  ext X
  simp [forwardSpanComparison, reverseSpanComparison, Category.assoc]
  have hn : L.map (α.hom.app (eO.functor.obj (eO.inverse.obj X))) ≫
      L.map (K.map (eO.counit.app X)) =
      L.map ((eO.inverse ⋙ J ⋙ eP.functor).map (eO.counit.app X)) ≫
        L.map (α.hom.app X) := by
    exact calc
      _ = L.map (α.hom.app (eO.functor.obj (eO.inverse.obj X)) ≫
          K.map (eO.counit.app X)) := (L.map_comp _ _).symm
      _ = L.map (((eO.inverse ⋙ J ⋙ eP.functor).map (eO.counit.app X)) ≫
          α.hom.app X) := congrArg L.map
            (α.hom.naturality (eO.counit.app X)).symm
      _ = L.map ((eO.inverse ⋙ J ⋙ eP.functor).map (eO.counit.app X)) ≫
          L.map (α.hom.app X) := L.map_comp _ _
  have hE : L.map (eP.counitInv.app (eP.functor.obj (J.obj (eO.inverse.obj X)))) ≫
      L.map (eP.functor.map (eP.unitIso.inv.app (J.obj (eO.inverse.obj X)))) = 𝟙 _ := by
    exact calc
      _ = L.map (eP.counitInv.app (eP.functor.obj (J.obj (eO.inverse.obj X))) ≫
          eP.functor.map (eP.unitIso.inv.app (J.obj (eO.inverse.obj X)))) :=
        (L.map_comp _ _).symm
      _ = L.map (𝟙 _) := congrArg L.map
        (eP.counitIso_functor_comp (J.obj (eO.inverse.obj X)))
      _ = 𝟙 _ := L.map_id _
  have hEassoc :
      L.map (eP.counitInv.app (eP.functor.obj (J.obj (eO.inverse.obj X)))) ≫
      L.map (eP.functor.map (eP.unitIso.inv.app (J.obj (eO.inverse.obj X)))) ≫
      L.map (eP.functor.map (J.map (eO.unit.app (eO.inverse.obj X)))) ≫
      L.map (α.hom.app (eO.functor.obj (eO.inverse.obj X))) ≫
      L.map (K.map (eO.counit.app X)) =
      L.map (eP.functor.map (J.map (eO.unit.app (eO.inverse.obj X)))) ≫
      L.map (α.hom.app (eO.functor.obj (eO.inverse.obj X))) ≫
      L.map (K.map (eO.counit.app X)) := by
    rw [← Category.assoc, hE]
    simp
  slice_lhs 3 7 => exact hEassoc
  slice_lhs 4 5 => exact hn
  have hu : eO.unit.app (eO.inverse.obj X) ≫
      eO.inverse.map (eO.counit.app X) = 𝟙 (eO.inverse.obj X) := by
    simp
  have ht : L.map (eP.functor.map (J.map (eO.unit.app (eO.inverse.obj X)))) ≫
      L.map ((eO.inverse ⋙ J ⋙ eP.functor).map (eO.counit.app X)) = 𝟙 _ := by
    change L.map (eP.functor.map (J.map (eO.unit.app (eO.inverse.obj X)))) ≫
      L.map (eP.functor.map (J.map (eO.inverse.map (eO.counit.app X)))) = 𝟙 _
    rw [← L.map_comp, ← eP.functor.map_comp, ← J.map_comp]
    simp
  have htassoc : L.map (eP.functor.map (J.map (eO.unit.app (eO.inverse.obj X)))) ≫
      L.map ((eO.inverse ⋙ J ⋙ eP.functor).map (eO.counit.app X)) ≫
      L.map (α.hom.app X) = L.map (α.hom.app X) := by
    rw [← Category.assoc, ht]
    exact Category.id_comp _
  slice_lhs 3 4 => exact htassoc
  slice_lhs 2 3 => exact calc
    _ = L.map (α.inv.app X ≫ α.hom.app X) := (L.map_comp _ _).symm
    _ = L.map (𝟙 _) := congrArg L.map (α.inv_hom_id_app X)
    _ = 𝟙 _ := L.map_id _
  simp

/-- Inverse orientation of `spanRoundTripIso_counit`. -/
theorem spanRoundTripIso_counit_inv
    (eO : O ≌ O') (eP : P ≌ P') (J : Functor O P) (K : Functor O' P')
    (α : eO.inverse ⋙ J ⋙ eP.functor ≅ K) (L : Functor P' C) :
    (eO.invFunIdAssoc (K ⋙ L)).inv ≫
        Functor.whiskerLeft eO.inverse
          (reverseSpanComparison eO eP J K α L).hom ≫
        (forwardSpanComparison eO eP J K α (eP.functor ⋙ L)).inv =
      Functor.whiskerLeft K ((eP.congrLeft).counitIso.inv.app L) := by
  let a := (forwardSpanComparison eO eP J K α (eP.functor ⋙ L)).trans
    ((Functor.isoWhiskerLeft eO.inverse
      (reverseSpanComparison eO eP J K α L).symm).trans
        (eO.invFunIdAssoc (K ⋙ L)))
  let b := Functor.isoWhiskerLeft K ((eP.congrLeft).counitIso.app L)
  have hab : a = b := Iso.ext (spanRoundTripIso_counit eO eP J K α L)
  simpa [a, b, Category.assoc] using congrArg Iso.inv hab

section ResidualExamples

variable (eO : O ≌ O') (eP : P ≌ P') (J : Functor O P) (K : Functor O' P')
  (α : eO.inverse ⋙ J ⋙ eP.functor ≅ K)

example (L : Functor P C) :
    (reverseSpanComparison eO eP J K α (eP.inverse ⋙ L)).inv ≫
        Functor.whiskerLeft eO.functor
          (forwardSpanComparison eO eP J K α L).hom ≫
        (eO.funInvIdAssoc (J ⋙ L)).hom =
      Functor.whiskerLeft J ((eP.congrLeft).unitIso.inv.app L) :=
  spanRoundTripIso_unit eO eP J K α L

example (L : Functor P' C) :
    (eO.invFunIdAssoc (K ⋙ L)).inv ≫
        Functor.whiskerLeft eO.inverse
          (reverseSpanComparison eO eP J K α L).hom ≫
        (forwardSpanComparison eO eP J K α (eP.functor ⋙ L)).inv =
      Functor.whiskerLeft K ((eP.congrLeft).counitIso.inv.app L) :=
  spanRoundTripIso_counit_inv eO eP J K α L

end ResidualExamples

#print axioms forwardSpanComparison
#print axioms reverseSpanComparison
#print axioms spanRoundTripIso_unit
#print axioms spanRoundTripIso_unit_inv
#print axioms spanRoundTripIso_counit
#print axioms spanRoundTripIso_counit_inv

end ConstructionTargets.EquivalenceSpanRoundTrip
