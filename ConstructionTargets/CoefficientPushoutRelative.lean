import ConstructionTargets.CoefficientRelativeSmall
noncomputable section
namespace ConstructionTargets.CoefficientPushoutRelative
open CategoryTheory CategoryTheory.Limits
open SingularExcision
variable (R : Type) [CommRing R]
abbrev chains := CoefficientRelativeSmall.chains R
/-- R and all simplicial-set degrees are Type 0. -/
instance preserves_pushouts : PreservesColimitsOfShape WalkingSpan (chains R) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  dsimp [chains, CoefficientRelativeSmall.chains, AlgebraicTopology.SSet.singularChainComplexFunctor]
  letI := (sigmaConstAdj (ModuleCat.of R R)).leftAdjoint_preservesColimits
  change PreservesColimitsOfShape WalkingSpan
    ((evaluation SimplexCategoryᵒᵖ Type).obj (Opposite.op (SimplexCategory.mk n)) ⋙
      sigmaConst.obj (ModuleCat.of R R))
  infer_instance

variable {W X Y Z : SSet} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

def relativeMap (sq : IsPushout f g h i) :
    cokernel ((chains R).map g) ⟶ cokernel ((chains R).map h) :=
  cokernel.map _ _ ((chains R).map f) ((chains R).map i) (sq.map (chains R)).flip.w

instance relativeMap_isIso (sq : IsPushout f g h i) : IsIso (relativeMap R sq) :=
  isIso_cokernel_map_of_isPushout (sq.map (chains R)).flip

def relativeIso (sq : IsPushout f g h i) :
    cokernel ((chains R).map g) ≅ cokernel ((chains R).map h) := asIso (relativeMap R sq)

theorem relativeIso_hom (sq : IsPushout f g h i) :
    (relativeIso R sq).hom =
      cokernel.map _ _ ((chains R).map f) ((chains R).map i) (sq.map (chains R)).flip.w := rfl

theorem projection (sq : IsPushout f g h i) :
    cokernel.π ((chains R).map g) ≫ (relativeIso R sq).hom =
      (chains R).map i ≫ cokernel.π ((chains R).map h) := by
  exact cokernel.π_desc _ _ _

theorem projection_degree (sq : IsPushout f g h i) (n : ℕ) :
    (cokernel.π ((chains R).map g)).f n ≫ (relativeIso R sq).hom.f n =
      ((chains R).map i).f n ≫ (cokernel.π ((chains R).map h)).f n :=
  congrArg (fun q => q.f n) (projection R sq)

theorem inverse_left (sq : IsPushout f g h i) :
    (relativeIso R sq).inv ≫ relativeMap R sq = 𝟙 _ := (relativeIso R sq).inv_hom_id

theorem inverse_right (sq : IsPushout f g h i) :
    relativeMap R sq ≫ (relativeIso R sq).inv = 𝟙 _ := (relativeIso R sq).hom_inv_id

def unionSquare {S : SSet} (P Q : S.Subcomplex) :=
  (show SSet.Subcomplex.BicartSq (P ⊓ Q) P Q (P ⊔ Q) from ⟨rfl,rfl⟩).isPushout

def unionRelativeIso {S : SSet} (P Q : S.Subcomplex) := relativeIso R (unionSquare P Q)

theorem union_projection {S : SSet} (P Q : S.Subcomplex) :
    cokernel.π ((chains R).map (subcomplexIntersectionToRight P Q)) ≫ (unionRelativeIso R P Q).hom =
      (chains R).map (subcomplexRightToUnion P Q) ≫
        cokernel.π ((chains R).map (subcomplexLeftToUnion P Q)) := projection R (unionSquare P Q)

def integral_union {S : SSet} (P Q : S.Subcomplex) := unionRelativeIso ℤ P Q
def rational_union {S : SSet} (P Q : S.Subcomplex) := unionRelativeIso ℚ P Q

#print axioms preserves_pushouts
#print axioms relativeMap_isIso
#print axioms projection_degree
#print axioms inverse_left
#print axioms inverse_right
#print axioms union_projection
#print axioms integral_union
#print axioms rational_union
end ConstructionTargets.CoefficientPushoutRelative
