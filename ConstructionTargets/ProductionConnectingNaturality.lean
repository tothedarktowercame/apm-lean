import ConstructionTargets.ProductionOpenCoverMayerVietoris

open CategoryTheory

noncomputable section

namespace ConstructionTargets.ProductionConnectingNaturality

private abbrev ssetChains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

/-- The exact chain-level prerequisite for naturality of the production
Mayer--Vietoris connecting morphism. -/
def MemberwiseCoverSmallNaturality : Prop :=
  ∀ {X Y α : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : α → Set X) (V : α → Set Y) (f : C(X, Y)),
    (∀ a, f '' U a ⊆ V a) →
    ∃ F : SingularSubdivision.coverSmallChains U ⟶
        SingularSubdivision.coverSmallChains V,
      F ≫ SingularSubdivision.coverSmallChains.ι V =
        SingularSubdivision.coverSmallChains.ι U ≫
          ssetChains.map (TopCat.toSSet.map (TopCat.ofHom f))

private def coverMemberMap
    {X Y α : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : α → Set X) (V : α → Set Y) (f : C(X, Y))
    (hf : ∀ a, f '' U a ⊆ V a) (a : α) :
    TopCat.of (U a) ⟶ TopCat.of (V a) :=
  TopCat.ofHom ⟨fun x => ⟨f x.1, hf a ⟨x.1, x.2, rfl⟩⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem coverMemberMap_comp
    {X Y α : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : α → Set X) (V : α → Set Y) (f : C(X, Y))
    (hf : ∀ a, f '' U a ⊆ V a) (a : α) :
    coverMemberMap U V f hf a ≫
        SingularSubdivision.coverSubspaceInclusion V a =
      SingularSubdivision.coverSubspaceInclusion U a ≫ TopCat.ofHom f := by
  ext x
  rfl

def memberwiseCoverSmallSSetMap
    {X Y α : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : α → Set X) (V : α → Set Y) (f : C(X, Y))
    (hf : ∀ a, f '' U a ⊆ V a) :
    (SingularSubdivision.coverSmallSSet U : SSet) ⟶
      (SingularSubdivision.coverSmallSSet V : SSet) := by
  apply (SingularSubdivision.coverSmallSSet V).lift
    ((SingularSubdivision.coverSmallSSet U).ι ≫
      TopCat.toSSet.map (TopCat.ofHom f))
  rw [SSet.Subcomplex.range_comp,
    show SSet.Subcomplex.range (SingularSubdivision.coverSmallSSet U).ι =
      SingularSubdivision.coverSmallSSet U from Subfunctor.range_ι _,
    SingularSubdivision.coverSmallSSet, SSet.Subcomplex.image_iSup]
  apply iSup_le
  intro a
  rw [← SSet.Subcomplex.range_comp]
  refine le_iSup_of_le a ?_
  rw [← TopCat.toSSet.map_comp, ← coverMemberMap_comp U V f hf a,
    TopCat.toSSet.map_comp, SSet.Subcomplex.range_comp]
  exact SSet.Subcomplex.image_le_range _ _

@[reassoc] theorem memberwiseCoverSmallSSetMap_comp_ι
    {X Y α : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : α → Set X) (V : α → Set Y) (f : C(X, Y))
    (hf : ∀ a, f '' U a ⊆ V a) :
    memberwiseCoverSmallSSetMap U V f hf ≫
        (SingularSubdivision.coverSmallSSet V).ι =
      (SingularSubdivision.coverSmallSSet U).ι ≫
        TopCat.toSSet.map (TopCat.ofHom f) := by
  exact SSet.Subcomplex.lift_ι _ _

noncomputable def memberwiseCoverSmallMap
    {X Y α : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (U : α → Set X) (V : α → Set Y) (f : C(X, Y))
    (hf : ∀ a, f '' U a ⊆ V a) :
    SingularSubdivision.coverSmallChains U ⟶
      SingularSubdivision.coverSmallChains V :=
  ssetChains.map (memberwiseCoverSmallSSetMap U V f hf)

theorem memberwiseCoverSmallNaturality :
    MemberwiseCoverSmallNaturality := by
  intro X Y α _ _ U V f hf
  refine ⟨memberwiseCoverSmallMap U V f hf, ?_⟩
  change ssetChains.map _ ≫ ssetChains.map _ =
    ssetChains.map _ ≫ ssetChains.map _
  rw [← ssetChains.map_comp, ← ssetChains.map_comp]
  congr 1

end ConstructionTargets.ProductionConnectingNaturality
