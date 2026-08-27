import ConstructionTargets.HomologyBiprodIso

/-!
# Homology normalization for binary biproduct maps

Component and reassembly formulas for the canonical comparison between the
homology of a binary biproduct of chain complexes and the binary biproduct of
their homology objects.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.HomologyBiprodNormalization

open ConstructionTargets.HomologyBiprodIso

variable {W K L T : ChainComplex AddCommGrpCat ℕ} (n : ℕ)

/-- After the canonical homology-biproduct comparison, the first component of
the homology map of a lift is the homology map of its first component. -/
theorem homologyMap_lift_biprodIso_fst (f : W ⟶ K) (g : W ⟶ L) :
    HomologicalComplex.homologyMap (biprod.lift f g) n ≫
        (homologyBiprodIso K L n).hom ≫ biprod.fst =
      HomologicalComplex.homologyMap f n := by
  calc
    _ = HomologicalComplex.homologyMap (biprod.lift f g) n ≫
        HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) n := by
          simp only [homologyBiprodIso_hom, biprod.lift_fst]
    _ = HomologicalComplex.homologyMap
        (biprod.lift f g ≫ (biprod.fst : K ⊞ L ⟶ K)) n := by
          rw [HomologicalComplex.homologyMap_comp]
    _ = _ := by rw [biprod.lift_fst]

/-- After the canonical homology-biproduct comparison, the second component
of the homology map of a lift is the homology map of its second component. -/
theorem homologyMap_lift_biprodIso_snd (f : W ⟶ K) (g : W ⟶ L) :
    HomologicalComplex.homologyMap (biprod.lift f g) n ≫
        (homologyBiprodIso K L n).hom ≫ biprod.snd =
      HomologicalComplex.homologyMap g n := by
  calc
    _ = HomologicalComplex.homologyMap (biprod.lift f g) n ≫
        HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) n := by
          simp only [homologyBiprodIso_hom, biprod.lift_snd]
    _ = HomologicalComplex.homologyMap
        (biprod.lift f g ≫ (biprod.snd : K ⊞ L ⟶ L)) n := by
          rw [HomologicalComplex.homologyMap_comp]
    _ = _ := by rw [biprod.lift_snd]

/-- The signed Mayer--Vietoris lift has the expected left homology
component. -/
theorem homologyMap_signedLift_biprodIso_fst (f : W ⟶ K) (g : W ⟶ L) :
    HomologicalComplex.homologyMap (biprod.lift f (-g)) n ≫
        (homologyBiprodIso K L n).hom ≫ biprod.fst =
      HomologicalComplex.homologyMap f n :=
  homologyMap_lift_biprodIso_fst n f (-g)

/-- The signed Mayer--Vietoris lift has the negated right homology
component. -/
theorem homologyMap_signedLift_biprodIso_snd (f : W ⟶ K) (g : W ⟶ L) :
    HomologicalComplex.homologyMap (biprod.lift f (-g)) n ≫
        (homologyBiprodIso K L n).hom ≫ biprod.snd =
      -HomologicalComplex.homologyMap g n := by
  rw [homologyMap_lift_biprodIso_snd, HomologicalComplex.homologyMap_neg]

section PostcomposeBiprodMap

variable {A B : AddCommGrpCat}

/-- The left component formula remains literal after applying an arbitrary
map to each output of the homology biproduct. -/
theorem homologyMap_signedLift_biprodIso_map_fst
    (f : W ⟶ K) (g : W ⟶ L)
    (u : K.homology n ⟶ A) (v : L.homology n ⟶ B) :
    HomologicalComplex.homologyMap (biprod.lift f (-g)) n ≫
        (homologyBiprodIso K L n).hom ≫ biprod.map u v ≫ biprod.fst =
      HomologicalComplex.homologyMap f n ≫ u := by
  calc
    _ = (HomologicalComplex.homologyMap (biprod.lift f (-g)) n ≫
          (homologyBiprodIso K L n).hom ≫ biprod.fst) ≫ u := by
        simp only [Category.assoc, biprod.map_fst]
    _ = _ := by rw [homologyMap_signedLift_biprodIso_fst]

/-- The right component after an arbitrary biproduct map retains the
Mayer--Vietoris minus sign. -/
theorem homologyMap_signedLift_biprodIso_map_snd
    (f : W ⟶ K) (g : W ⟶ L)
    (u : K.homology n ⟶ A) (v : L.homology n ⟶ B) :
    HomologicalComplex.homologyMap (biprod.lift f (-g)) n ≫
        (homologyBiprodIso K L n).hom ≫ biprod.map u v ≫ biprod.snd =
      (-HomologicalComplex.homologyMap g n) ≫ v := by
  calc
    _ = (HomologicalComplex.homologyMap (biprod.lift f (-g)) n ≫
          (homologyBiprodIso K L n).hom ≫ biprod.snd) ≫ v := by
        simp only [Category.assoc, biprod.map_snd]
    _ = _ := by rw [homologyMap_signedLift_biprodIso_snd]

section WhiskerLeft

variable {X : AddCommGrpCat}

/-- The postcomposed left-component formula is stable under an arbitrary
prefix into the source homology object, in the association used by downstream
exact-sequence composites. -/
theorem whiskerLeft_homologyMap_signedLift_biprodIso_map_fst
    (a : X ⟶ W.homology n) (f : W ⟶ K) (g : W ⟶ L)
    (u : K.homology n ⟶ A) (v : L.homology n ⟶ B) :
    a ≫ HomologicalComplex.homologyMap (biprod.lift f (-g)) n ≫
        (((homologyBiprodIso K L n).hom ≫ biprod.map u v) ≫ biprod.fst) =
      a ≫ HomologicalComplex.homologyMap f n ≫ u := by
  calc
    _ = a ≫
        (HomologicalComplex.homologyMap (biprod.lift f (-g)) n ≫
          (homologyBiprodIso K L n).hom ≫ biprod.map u v ≫ biprod.fst) := by
        simp only [Category.assoc]
    _ = a ≫ (HomologicalComplex.homologyMap f n ≫ u) := by
        rw [homologyMap_signedLift_biprodIso_map_fst]
    _ = _ := rfl

/-- The postcomposed right-component formula, with its Mayer--Vietoris sign,
is stable under an arbitrary prefix into the source homology object. -/
theorem whiskerLeft_homologyMap_signedLift_biprodIso_map_snd
    (a : X ⟶ W.homology n) (f : W ⟶ K) (g : W ⟶ L)
    (u : K.homology n ⟶ A) (v : L.homology n ⟶ B) :
    a ≫ HomologicalComplex.homologyMap (biprod.lift f (-g)) n ≫
        (((homologyBiprodIso K L n).hom ≫ biprod.map u v) ≫ biprod.snd) =
      a ≫ (-HomologicalComplex.homologyMap g n) ≫ v := by
  calc
    _ = a ≫
        (HomologicalComplex.homologyMap (biprod.lift f (-g)) n ≫
          (homologyBiprodIso K L n).hom ≫ biprod.map u v ≫ biprod.snd) := by
        simp only [Category.assoc]
    _ = a ≫ ((-HomologicalComplex.homologyMap g n) ≫ v) := by
        rw [homologyMap_signedLift_biprodIso_map_snd]
    _ = _ := rfl

/-- Fully left-associated spelling of the whiskered left-component formula.
This is the literal association produced by the production composite. -/
theorem fullyLeftAssociated_homologyMap_signedLift_biprodIso_map_fst
    (a : X ⟶ W.homology n) (f : W ⟶ K) (g : W ⟶ L)
    (u : K.homology n ⟶ A) (v : L.homology n ⟶ B) :
    ((((a ≫ HomologicalComplex.homologyMap (biprod.lift f (-g)) n) ≫
          (homologyBiprodIso K L n).hom) ≫ biprod.map u v) ≫ biprod.fst) =
      ((a ≫ HomologicalComplex.homologyMap f n) ≫ u) := by
  simpa only [Category.assoc] using
    whiskerLeft_homologyMap_signedLift_biprodIso_map_fst n a f g u v

/-- Fully left-associated spelling of the whiskered signed right-component
formula, again matching the literal production composite. -/
theorem fullyLeftAssociated_homologyMap_signedLift_biprodIso_map_snd
    (a : X ⟶ W.homology n) (f : W ⟶ K) (g : W ⟶ L)
    (u : K.homology n ⟶ A) (v : L.homology n ⟶ B) :
    ((((a ≫ HomologicalComplex.homologyMap (biprod.lift f (-g)) n) ≫
          (homologyBiprodIso K L n).hom) ≫ biprod.map u v) ≫ biprod.snd) =
      ((a ≫ (-HomologicalComplex.homologyMap g n)) ≫ v) := by
  simpa only [Category.assoc] using
    whiskerLeft_homologyMap_signedLift_biprodIso_map_snd n a f g u v

end WhiskerLeft

end PostcomposeBiprodMap

/-- Mapping the canonical homology biproduct back into homology of the chain
biproduct and then along a chain-level descent map gives the homology maps of
the two descent components. -/
theorem biprod_inl_homologyBiprodIso_inv_homologyMap_desc
    (f : K ⟶ T) (g : L ⟶ T) :
    biprod.inl ≫ (homologyBiprodIso K L n).inv ≫
        HomologicalComplex.homologyMap (biprod.desc f g) n =
      HomologicalComplex.homologyMap f n := by
  rw [homologyBiprodIso_inv, biprod.inl_desc_assoc,
    ← HomologicalComplex.homologyMap_comp, biprod.inl_desc]

theorem biprod_inr_homologyBiprodIso_inv_homologyMap_desc
    (f : K ⟶ T) (g : L ⟶ T) :
    biprod.inr ≫ (homologyBiprodIso K L n).inv ≫
        HomologicalComplex.homologyMap (biprod.desc f g) n =
      HomologicalComplex.homologyMap g n := by
  rw [homologyBiprodIso_inv, biprod.inr_desc_assoc,
    ← HomologicalComplex.homologyMap_comp, biprod.inr_desc]

/-- Full reassembly of a chain-level descent map after transporting out of
the homology biproduct. -/
theorem homologyBiprodIso_inv_homologyMap_desc
    (f : K ⟶ T) (g : L ⟶ T) :
    (homologyBiprodIso K L n).inv ≫
        HomologicalComplex.homologyMap (biprod.desc f g) n =
      biprod.desc (HomologicalComplex.homologyMap f n)
        (HomologicalComplex.homologyMap g n) := by
  apply biprod.hom_ext'
  · simpa only [biprod.inl_desc] using
      biprod_inl_homologyBiprodIso_inv_homologyMap_desc n f g
  · simpa only [biprod.inr_desc] using
      biprod_inr_homologyBiprodIso_inv_homologyMap_desc n f g

#print axioms homologyMap_signedLift_biprodIso_fst
#print axioms homologyMap_signedLift_biprodIso_snd
#print axioms homologyMap_signedLift_biprodIso_map_fst
#print axioms homologyMap_signedLift_biprodIso_map_snd
#print axioms whiskerLeft_homologyMap_signedLift_biprodIso_map_fst
#print axioms whiskerLeft_homologyMap_signedLift_biprodIso_map_snd
#print axioms fullyLeftAssociated_homologyMap_signedLift_biprodIso_map_fst
#print axioms fullyLeftAssociated_homologyMap_signedLift_biprodIso_map_snd
#print axioms homologyBiprodIso_inv_homologyMap_desc

end ConstructionTargets.HomologyBiprodNormalization
