import ConstructionTargets.TorusCircleWedgeMappingEquivalence

/-!
# Source reconstruction from target-natural mapping-category equivalences

A family of equivalences `(A ⥤ C) ≌ (B ⥤ C)`, natural under
postcomposition, reconstructs an equivalence `A ≌ B`.  The torus-circle wedge
mapping equivalence then gives its fundamental groupoid a single-object model
and identifies the endomorphism group at the displayed wedge base.
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.GenericTargetNaturalSourceReconstruction

universe u
variable {A B : Type u} [Category A] [Category B]

variable (E : ∀ (C : Type u) [Category C], (A ⥤ C) ≌ (B ⥤ C))
variable (postIso : ∀ {C D : Type u} [Category C] [Category D] (K : C ⥤ D),
  (Functor.whiskeringRight A C D).obj K ⋙ (E D).functor ≅
    (E C).functor ⋙ (Functor.whiskeringRight B C D).obj K)

def forwardCandidate : A ⥤ B := (E B).inverse.obj (𝟭 B)

def inverseCandidate : B ⥤ A := (E A).functor.obj (𝟭 A)

@[reducible] def targetSquare {C D : Type u} [Category C] [Category D]
    (K : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight A C D).obj K) (E C).functor (E D).functor
    ((Functor.whiskeringRight B C D).obj K) where
  iso := postIso K

@[reducible] def inverseTargetSquare {C D : Type u} [Category C] [Category D]
    (K : C ⥤ D) : CatCommSq
    ((Functor.whiskeringRight B C D).obj K) (E C).inverse (E D).inverse
    ((Functor.whiskeringRight A C D).obj K) :=
  CatCommSq.vInv _ (E C) (E D) _ (targetSquare E postIso K)

def forwardRoundTripImageIso :
    (E A).functor.obj (forwardCandidate E ⋙ inverseCandidate E) ≅
      (E A).functor.obj (𝟭 A) :=
  (postIso (inverseCandidate E)).app (forwardCandidate E) ≪≫
    Functor.isoWhiskerRight ((E B).counitIso.app (𝟭 B)) (inverseCandidate E) ≪≫
    Functor.leftUnitor (inverseCandidate E)

def forwardRoundTripIso :
    forwardCandidate E ⋙ inverseCandidate E ≅ 𝟭 A :=
  (E A).functor.preimageIso (forwardRoundTripImageIso E postIso)

def inverseRoundTripImageIso :
    (E B).inverse.obj (inverseCandidate E ⋙ forwardCandidate E) ≅
      (E B).inverse.obj (𝟭 B) :=
  (inverseTargetSquare E postIso (forwardCandidate E)).iso.app (inverseCandidate E) ≪≫
    Functor.isoWhiskerRight ((E A).unitIso.app (𝟭 A)).symm (forwardCandidate E) ≪≫
    Functor.leftUnitor (forwardCandidate E)

def inverseRoundTripIso :
    inverseCandidate E ⋙ forwardCandidate E ≅ 𝟭 B :=
  (E B).inverse.preimageIso (inverseRoundTripImageIso E postIso)

/-- Reconstruct the source equivalence from the target-natural family of
mapping-category equivalences. -/
def sourceEquivalence : A ≌ B :=
  CategoryTheory.Equivalence.mk (forwardCandidate E) (inverseCandidate E)
    (forwardRoundTripIso E postIso).symm (inverseRoundTripIso E postIso)

@[simp] theorem sourceEquivalence_functor :
    (sourceEquivalence E postIso).functor = forwardCandidate E := rfl

@[simp] theorem sourceEquivalence_inverse :
    (sourceEquivalence E postIso).inverse = inverseCandidate E := rfl

open ConstructionTargets.TorusCircleWedgeMappingEquivalence
open ConstructionTargets.TorusCircleWedgeOpenCover

abbrev FP := Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ)

def wedgeSourceEquivalence :
    FundamentalGroupoid GenericWedge ≌ SingleObj FP :=
  sourceEquivalence
    (fun C _ => genericWedgeSingleObjMappingEquivalence C)
    (fun K => genericWedgeSingleObjPostcomposeIso K)

/-- The image of the torus basepoint in the explicit point-wedge quotient. -/
def wedgeBase : GenericWedge :=
  ConstructionTargets.PointWedgeQuotient.quotientMap
    ((1, 1) : Circle × Circle) (1 : Circle) (.inl (1, 1))

theorem wedgeSourceEquivalence_base_obj :
    wedgeSourceEquivalence.functor.obj (FundamentalGroupoid.mk wedgeBase) =
      SingleObj.star FP := by
  exact Subsingleton.elim _ _

/-- The wedge fundamental group, oriented from loops at the displayed source
basepoint to the torus-first/circle-second free product. -/
def wedgeFundamentalGroupMulEquiv :
    FundamentalGroup GenericWedge wedgeBase ≃* FP :=
  (wedgeSourceEquivalence.fullyFaithfulFunctor.mulEquivEnd
      (FundamentalGroupoid.mk wedgeBase)).trans
    ((Iso.conj (eqToIso wedgeSourceEquivalence_base_obj)).trans
      (SingleObj.toEnd FP).symm)

#print axioms sourceEquivalence
#print axioms wedgeSourceEquivalence
#print axioms wedgeFundamentalGroupMulEquiv

end ConstructionTargets.GenericTargetNaturalSourceReconstruction
