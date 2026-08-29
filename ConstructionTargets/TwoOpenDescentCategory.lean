import ConstructionTargets.TwoOpenDescentReconstruction

/-!
# The category of two-open descent data
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenDescentCategory

open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.TwoOpenDescentRestriction
open ConstructionTargets.TwoOpenDescentFullness
open ConstructionTargets.TwoOpenDescentFullness.CompatibleNatTrans
open ConstructionTargets.TwoOpenDescentReconstruction
open ConstructionTargets.TwoOpenDescentFunctor

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

theorem eqToHom_self_inv_hom {A B : C} (r : A = A) (h : B = A) :
    eqToHom r.symm ≫ eqToHom h.symm ≫ eqToHom h = 𝟙 A := by
  subst B
  simp

theorem eqToHom_inv_hom_self {A B : C} (h : B = A) (r : A = A) :
    eqToHom h.symm ≫ eqToHom h ≫ eqToHom r = 𝟙 A := by
  subst B
  simp

/-- Objects of the category of two-open descent data. -/
structure DescentObject where
  datum : @TwoOpenDescentDatum X _ U V C _

/-- Identity compatible transformation. -/
def compatibleId (D : @TwoOpenDescentDatum X _ U V C _) :
    CompatibleNatTrans D D where
  piece _ := 𝟙 _
  overlap_app := by
    intro x hU hV
    unfold transportedPieceApp
    simp

theorem transportedPieceApp_comp
    {D E K : @TwoOpenDescentDatum X _ U V C _}
    (τ : CompatibleNatTrans D E) (σ : CompatibleNatTrans E K)
    (b : Bool) (z : FundamentalGroupoid (CoverPiece U V b)) :
    transportedPieceApp D K (τ.piece b ≫ σ.piece b) z =
      transportedPieceApp D E (τ.piece b) z ≫
        transportedPieceApp E K (σ.piece b) z := by
  unfold transportedPieceApp
  simp only [NatTrans.comp_app, Category.assoc]
  simp

/-- Composition of compatible transformations. -/
def compatibleComp
    {D E K : @TwoOpenDescentDatum X _ U V C _}
    (τ : CompatibleNatTrans D E) (σ : CompatibleNatTrans E K) :
    CompatibleNatTrans D K where
  piece b := τ.piece b ≫ σ.piece b
  overlap_app := by
    intro x hU hV
    rw [transportedPieceApp_comp τ σ false,
      transportedPieceApp_comp τ σ true]
    rw [τ.overlap_app x hU hV, σ.overlap_app x hU hV]

@[ext] theorem CompatibleNatTrans.ext
    {D E : @TwoOpenDescentDatum X _ U V C _}
    {τ σ : CompatibleNatTrans D E}
    (h : ∀ b, τ.piece b = σ.piece b) : τ = σ := by
  cases τ with
  | mk τ hτ =>
    cases σ with
    | mk σ hσ =>
      simp only [CompatibleNatTrans.mk.injEq]
      funext b
      exact h b

instance : Category (DescentObject (X := X) (U := U) (V := V) (C := C)) where
  Hom D E := CompatibleNatTrans D.datum E.datum
  id D := compatibleId D.datum
  comp τ σ := compatibleComp τ σ
  id_comp := by
    intro D E τ
    apply CompatibleNatTrans.ext
    intro b
    simp [compatibleId, compatibleComp]
  comp_id := by
    intro D E τ
    apply CompatibleNatTrans.ext
    intro b
    simp [compatibleId, compatibleComp]
  assoc := by
    intro A B D E τ σ κ
    apply CompatibleNatTrans.ext
    intro b
    simp [compatibleComp, Category.assoc]

/-- Whiskering an ambient natural transformation gives compatible
transformations between the canonical restrictions. -/
def canonicalCompatibleNatTrans {F G : FundamentalGroupoid X ⥤ C}
    (α : F ⟶ G) :
    CompatibleNatTrans
      (canonicalTwoOpenDescentDatum (U := U) (V := V) F)
      (canonicalTwoOpenDescentDatum (U := U) (V := V) G) where
  piece b := Functor.whiskerLeft (FundamentalGroupoid.map (coverPieceInclusion b)) α
  overlap_app := by
    intro x hU hV
    unfold transportedPieceApp
    change (𝟙 _) ≫ α.app ⟨x⟩ ≫ (𝟙 _) =
      (𝟙 _) ≫ α.app ⟨x⟩ ≫ (𝟙 _)
    simp

/-- Restriction from ambient fundamental-groupoid functors to descent data. -/
def restrictionFunctor :
    (FundamentalGroupoid X ⥤ C) ⥤
      DescentObject (X := X) (U := U) (V := V) (C := C) where
  obj F := ⟨canonicalTwoOpenDescentDatum (U := U) (V := V) F⟩
  map α := canonicalCompatibleNatTrans α
  map_id _ := by
    apply CompatibleNatTrans.ext
    intro b
    ext z
    rfl
  map_comp _ _ := by
    apply CompatibleNatTrans.ext
    intro b
    ext z
    rfl

/-- Reconstruction sends compatible piece transformations to their glued
ambient natural transformation. -/
def reconstructionFunctor (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    DescentObject (X := X) (U := U) (V := V) (C := C) ⥤
      (FundamentalGroupoid X ⥤ C) where
  obj D := twoOpenDescentFunctor hU hV hcover D.datum
  map τ := τ.ambientNatTrans hU hV hcover
  map_id D := by
    ext x
    change (compatibleId D.datum).ambientApp hcover x.as = 𝟙 _
    have hx : x.as ∈ U ∪ V := by rw [hcover]; trivial
    rcases hx with hxU | hxV
    · rw [ambientApp_eq_true hcover _ _ hxU]
      unfold chartApp transportedPieceApp compatibleId
      simp
    · rw [ambientApp_eq_false hcover _ _ hxV]
      unfold chartApp transportedPieceApp compatibleId
      simp
  map_comp τ σ := by
    ext x
    change (compatibleComp τ σ).ambientApp hcover x.as =
      τ.ambientApp hcover x.as ≫ σ.ambientApp hcover x.as
    have hx : x.as ∈ U ∪ V := by rw [hcover]; trivial
    rcases hx with hxU | hxV
    · rw [ambientApp_eq_true hcover _ _ hxU,
        ambientApp_eq_true hcover τ _ hxU,
        ambientApp_eq_true hcover σ _ hxU]
      unfold chartApp
      exact transportedPieceApp_comp τ σ true _
    · rw [ambientApp_eq_false hcover _ _ hxV,
        ambientApp_eq_false hcover τ _ hxV,
        ambientApp_eq_false hcover σ _ hxV]
      unfold chartApp
      exact transportedPieceApp_comp τ σ false _

/-- The reconstructed canonical restriction is naturally isomorphic to the
original ambient functor. -/
def reconstructionRestrictionIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    restrictionFunctor (X := X) (U := U) (V := V) (C := C) ⋙
        reconstructionFunctor hU hV hcover ≅
      𝟭 (FundamentalGroupoid X ⥤ C) :=
  NatIso.ofComponents (canonicalReconstructionIso hU hV hcover) (by
    intro F G α
    ext x
    simp [restrictionFunctor, reconstructionFunctor,
      canonicalCompatibleNatTrans, canonicalReconstructionIso,
      canonicalReconstructionAppIso, ambientNatTrans, ambientComponent]
    have hx : x.as ∈ U ∪ V := by rw [hcover]; trivial
    rcases hx with hxU | hxV
    · rw [ambientApp_eq_true hcover _ _ hxU]
      unfold chartApp transportedPieceApp
      change (𝟙 _) ≫ α.app ⟨x.as⟩ ≫ (𝟙 _) = α.app x
      cases x
      simp
    · rw [ambientApp_eq_false hcover _ _ hxV]
      unfold chartApp transportedPieceApp
      change (𝟙 _) ≫ α.app ⟨x.as⟩ ≫ (𝟙 _) = α.app x
      cases x
      simp)

@[simp] theorem pieceRestrictionIso_hom_app
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) (b : Bool)
    (z : FundamentalGroupoid (CoverPiece U V b)) :
    (pieceRestrictionIso hU hV hcover D b).hom.app z =
      (eqToIso (D.obj_eq b z)).hom := rfl

@[simp] theorem pieceRestrictionIso_inv_app
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) (b : Bool)
    (z : FundamentalGroupoid (CoverPiece U V b)) :
    (pieceRestrictionIso hU hV hcover D b).inv.app z =
      (eqToIso (D.obj_eq b z)).inv := rfl

/-- The forward component on the descent side: restrict a reconstructed datum
and return to the supplied piece functors using the inverse restriction
isomorphisms. -/
def descentReconstructionHom (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : DescentObject (X := X) (U := U) (V := V) (C := C)) :
    CompatibleNatTrans
      (canonicalTwoOpenDescentDatum (U := U) (V := V)
        (twoOpenDescentFunctor hU hV hcover D.datum))
      D.datum where
  piece b := (pieceRestrictionIso hU hV hcover D.datum b).inv
  overlap_app := by
    intro x hxU hxV
    let zF : FundamentalGroupoid (CoverPiece U V false) :=
      ⟨⟨x, by simpa [twoChart] using hxV⟩⟩
    let zT : FundamentalGroupoid (CoverPiece U V true) :=
      ⟨⟨x, by simpa [twoChart] using hxU⟩⟩
    change transportedPieceApp _ _ _ zF = transportedPieceApp _ _ _ zT
    unfold transportedPieceApp
    rw [pieceRestrictionIso_inv_app, pieceRestrictionIso_inv_app]
    exact (eqToHom_self_inv_hom
      ((canonicalTwoOpenDescentDatum (U := U) (V := V)
        (twoOpenDescentFunctor hU hV hcover D.datum)).obj_eq false zF)
      (D.datum.obj_eq false zF)).trans
      (eqToHom_self_inv_hom
        ((canonicalTwoOpenDescentDatum (U := U) (V := V)
          (twoOpenDescentFunctor hU hV hcover D.datum)).obj_eq true zT)
        (D.datum.obj_eq true zT)).symm

/-- The inverse descent-side component, using the forward restriction
isomorphisms. -/
def descentReconstructionInv (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : DescentObject (X := X) (U := U) (V := V) (C := C)) :
    CompatibleNatTrans D.datum
      (canonicalTwoOpenDescentDatum (U := U) (V := V)
        (twoOpenDescentFunctor hU hV hcover D.datum)) where
  piece b := (pieceRestrictionIso hU hV hcover D.datum b).hom
  overlap_app := by
    intro x hxU hxV
    let zF : FundamentalGroupoid (CoverPiece U V false) :=
      ⟨⟨x, by simpa [twoChart] using hxV⟩⟩
    let zT : FundamentalGroupoid (CoverPiece U V true) :=
      ⟨⟨x, by simpa [twoChart] using hxU⟩⟩
    change transportedPieceApp _ _ _ zF = transportedPieceApp _ _ _ zT
    unfold transportedPieceApp
    rw [pieceRestrictionIso_hom_app, pieceRestrictionIso_hom_app]
    exact (eqToHom_inv_hom_self (D.datum.obj_eq false zF)
      ((canonicalTwoOpenDescentDatum (U := U) (V := V)
        (twoOpenDescentFunctor hU hV hcover D.datum)).obj_eq false zF)).trans
      (eqToHom_inv_hom_self (D.datum.obj_eq true zT)
        ((canonicalTwoOpenDescentDatum (U := U) (V := V)
          (twoOpenDescentFunctor hU hV hcover D.datum)).obj_eq true zT)).symm

/-- Restriction after reconstruction is isomorphic to the original descent
object. -/
def descentReconstructionAppIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : DescentObject (X := X) (U := U) (V := V) (C := C)) :
    (reconstructionFunctor hU hV hcover ⋙
      restrictionFunctor (X := X) (U := U) (V := V) (C := C)).obj D ≅ D where
  hom := descentReconstructionHom hU hV hcover D
  inv := descentReconstructionInv hU hV hcover D
  hom_inv_id := by
    apply CompatibleNatTrans.ext
    intro b
    exact (pieceRestrictionIso hU hV hcover D.datum b).inv_hom_id
  inv_hom_id := by
    apply CompatibleNatTrans.ext
    intro b
    exact (pieceRestrictionIso hU hV hcover D.datum b).hom_inv_id

/-- The descent-side reconstruction isomorphism is natural in compatible
piece transformations. -/
def descentReconstructionIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    reconstructionFunctor hU hV hcover ⋙
        restrictionFunctor (X := X) (U := U) (V := V) (C := C) ≅
      𝟭 (DescentObject (X := X) (U := U) (V := V) (C := C)) :=
  NatIso.ofComponents (descentReconstructionAppIso hU hV hcover) (by
    intro D E τ
    apply CompatibleNatTrans.ext
    intro b
    ext z
    change (Functor.whiskerLeft
          (FundamentalGroupoid.map (coverPieceInclusion b))
          (τ.ambientNatTrans hU hV hcover)).app z ≫
        (restrictionAppIso hU hV hcover E.datum b z).inv =
      (restrictionAppIso hU hV hcover D.datum b z).inv ≫
        (τ.piece b).app z
    have hn := τ.ambientNatTrans_restriction_app hU hV hcover b z
    calc
      _ = (restrictionAppIso hU hV hcover D.datum b z).inv ≫
          ((restrictionAppIso hU hV hcover D.datum b z).hom ≫
            (Functor.whiskerLeft
              (FundamentalGroupoid.map (coverPieceInclusion b))
              (τ.ambientNatTrans hU hV hcover)).app z) ≫
          (restrictionAppIso hU hV hcover E.datum b z).inv := by
            simp
            rfl
      _ = (restrictionAppIso hU hV hcover D.datum b z).inv ≫
          ((τ.piece b).app z ≫
            (restrictionAppIso hU hV hcover E.datum b z).hom) ≫
          (restrictionAppIso hU hV hcover E.datum b z).inv := by
            rw [hn]
            rfl
      _ = _ := by
        simp)

/-- Ambient fundamental-groupoid functors are equivalent to compatible
two-open descent data. -/
def twoOpenDescentEquivalence (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    (FundamentalGroupoid X ⥤ C) ≌
      DescentObject (X := X) (U := U) (V := V) (C := C) :=
  CategoryTheory.Equivalence.mk
    (restrictionFunctor (X := X) (U := U) (V := V) (C := C))
    (reconstructionFunctor hU hV hcover)
    (reconstructionRestrictionIso hU hV hcover).symm
    (descentReconstructionIso hU hV hcover)

#print axioms compatibleId
#print axioms compatibleComp
#print axioms restrictionFunctor
#print axioms reconstructionFunctor
#print axioms reconstructionRestrictionIso
#print axioms descentReconstructionHom
#print axioms descentReconstructionInv
#print axioms descentReconstructionAppIso
#print axioms descentReconstructionIso
#print axioms twoOpenDescentEquivalence

end ConstructionTargets.TwoOpenDescentCategory
