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

#print axioms compatibleId
#print axioms compatibleComp
#print axioms restrictionFunctor
#print axioms reconstructionFunctor
#print axioms reconstructionRestrictionIso

end ConstructionTargets.TwoOpenDescentCategory
