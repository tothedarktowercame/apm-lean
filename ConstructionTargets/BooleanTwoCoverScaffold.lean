import ConstructionTargets.SingularExcision

/-!
# Definition-first Boolean two-cover scaffold

The two range subcomplexes are primary data. Their infimum and supremum are
therefore definitionally the source and target of the subcomplex
Mayer--Vietoris short complex; the generic Boolean cover is compared only at
the outer boundary of the construction.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.BooleanTwoCoverScaffold

open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision

private abbrev ssetChains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

def booleanCover {X : Type} (U V : Set X) : Bool → Set X
  | true => U
  | false => V

def leftRange {X : Type} [TopologicalSpace X] (U : Set X) :
    (TopCat.toSSet.obj (TopCat.of X)).Subcomplex :=
  ambientSubspaceRange U

def rightRange {X : Type} [TopologicalSpace X] (V : Set X) :
    (TopCat.toSSet.obj (TopCat.of X)).Subcomplex :=
  ambientSubspaceRange V

def smallSSet {X : Type} [TopologicalSpace X] (U V : Set X) :
    (TopCat.toSSet.obj (TopCat.of X)).Subcomplex :=
  leftRange U ⊔ rightRange V

theorem coverSmallSSet_booleanCover
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    coverSmallSSet (booleanCover U V) = smallSSet U V := by
  rw [coverSmallSSet_bool_eq_sup]
  rfl

/-- Concrete inclusion-map identification of the stored Boolean union with
the generic cover-small subcomplex. -/
def smallSSetIsoCoverSmall
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    (smallSSet U V : SSet) ≅
      (coverSmallSSet (booleanCover U V) : SSet) where
  hom := SSet.Subcomplex.homOfLE (by
    rw [coverSmallSSet_booleanCover])
  inv := SSet.Subcomplex.homOfLE (by
    rw [coverSmallSSet_booleanCover])
  hom_inv_id := by rfl
  inv_hom_id := by rfl

/-- The concrete Boolean-union identification commutes with inclusion into
the ambient singular simplicial set. -/
theorem smallSSetIsoCoverSmall_hom_comp_ambient
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    (smallSSetIsoCoverSmall U V).hom ≫
        (coverSmallSSet (booleanCover U V)).ι =
      (smallSSet U V).ι := by
  rfl

/-- The stored left member inclusion agrees with the generic Boolean-cover
member inclusion after the concrete union identification. -/
theorem leftToSmall_comp_smallSSetIsoCoverSmall
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    subcomplexLeftToUnion (leftRange U) (rightRange V) ≫
        (smallSSetIsoCoverSmall U V).hom =
      coverMemberRangeInclusion (booleanCover U V) true := by
  rfl

/-- The stored right member inclusion agrees with the generic Boolean-cover
member inclusion after the concrete union identification. -/
theorem rightToSmall_comp_smallSSetIsoCoverSmall
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    subcomplexRightToUnion (leftRange U) (rightRange V) ≫
        (smallSSetIsoCoverSmall U V).hom =
      coverMemberRangeInclusion (booleanCover U V) false := by
  rfl

noncomputable def shortComplex
    {X : Type} [TopologicalSpace X] (U V : Set X) :=
  subcomplexMayerVietorisShortComplex (leftRange U) (rightRange V)

/-- Reassembly in the stored union, followed by its ambient inclusion, is
literally the descent of the two ambient range inclusions. -/
theorem reassembly_comp_ambient
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    (shortComplex U V).g ≫ ssetChains.map (smallSSet U V).ι =
      biprod.desc
        (ssetChains.map (leftRange U).ι)
        (ssetChains.map (rightRange V).ι) := by
  dsimp [shortComplex, subcomplexMayerVietorisShortComplex]
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, biprod.inl_desc]
    rw [← Functor.map_comp]
    rfl

  · rw [biprod.inr_desc_assoc, biprod.inr_desc]
    rw [← Functor.map_comp]
    rfl

/-- Fixture: the intersection and union objects are definitionally built from
the same two stored ranges, so all four canonical arrows type without an
equality transport. -/
example {X : Type} [TopologicalSpace X] (U V : Set X) :
    IsPushout
      (ssetChains.map (subcomplexIntersectionToLeft
        (leftRange U) (rightRange V)))
      (ssetChains.map (subcomplexIntersectionToRight
        (leftRange U) (rightRange V)))
      (ssetChains.map (subcomplexLeftToUnion
        (leftRange U) (rightRange V)))
      (ssetChains.map (subcomplexRightToUnion
        (leftRange U) (rightRange V))) :=
  subcomplexChains_isPushout (leftRange U) (rightRange V)

end ConstructionTargets.BooleanTwoCoverScaffold

#print axioms ConstructionTargets.BooleanTwoCoverScaffold.coverSmallSSet_booleanCover
#print axioms ConstructionTargets.BooleanTwoCoverScaffold.reassembly_comp_ambient
