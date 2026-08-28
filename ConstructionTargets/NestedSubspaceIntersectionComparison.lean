import ConstructionTargets.ProductionPairConnectingMayerVietorisComparison

/-!
# Comparing an intersection with a nested subspace

For sets `U V : Set X`, the ordinary intersection subtype `U ∩ V` and the
subspace of `V` cut out by `U` are canonically homeomorphic.  This file records
that homeomorphism and its naturality with the inclusions into `V`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.NestedSubspaceIntersectionComparison

open ConstructionTargets.SingularHomologyConcrete

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The subset of `V` whose underlying points lie in `U`. -/
def nestedIntersection : Set V := {x | (x.1 : X) ∈ U}

/-- Reassociate the two subtype predicates defining an intersection. -/
def intersectionNestedHomeomorph :
    (U ∩ V : Set X) ≃ₜ nestedIntersection U V where
  toFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  invFun x := ⟨x.1.1, x.2, x.1.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

@[simp] theorem intersectionNestedHomeomorph_apply_val
    (x : (U ∩ V : Set X)) :
    ((intersectionNestedHomeomorph U V x).1.1 : X) = x.1 := rfl

@[simp] theorem intersectionNestedHomeomorph_symm_apply_val
    (x : nestedIntersection U V) :
    ((intersectionNestedHomeomorph U V).symm x).1 = x.1.1 := rfl

/-- The direct inclusion of the ordinary intersection into `V`. -/
def intersectionToRightContinuous : C((U ∩ V : Set X), V) :=
  ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- Inclusion of the nested intersection into its ambient subtype `V`. -/
def nestedIntersectionInclusionContinuous :
    C(nestedIntersection U V, V) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The homeomorphism followed by nested-subspace inclusion is literally the
ordinary intersection inclusion. -/
theorem intersectionNested_continuous_square :
    (nestedIntersectionInclusionContinuous U V).comp
        ⟨intersectionNestedHomeomorph U V,
          (intersectionNestedHomeomorph U V).continuous⟩ =
      intersectionToRightContinuous U V := by
  ext x
  rfl

/-- The same square in `TopCat`, ready for functorial transport. -/
theorem intersectionNested_topCat_square :
    (TopCat.isoOfHomeo (intersectionNestedHomeomorph U V)).hom ≫
        TopCat.ofHom (nestedIntersectionInclusionContinuous U V) =
      TopCat.ofHom (intersectionToRightContinuous U V) := by
  ext x
  rfl

private abbrev singularChainsFunctor :=
  (AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

/-- The induced isomorphism of integral singular-chain complexes. -/
noncomputable def intersectionNestedChainsIso :
    SingularChains (TopCat.of (U ∩ V : Set X)) ≅
      SingularChains (TopCat.of (nestedIntersection U V)) :=
  singularChainsFunctor.mapIso
    (TopCat.isoOfHomeo (intersectionNestedHomeomorph U V))

/-- Chain-level naturality of the nested-intersection comparison. -/
theorem intersectionNested_chain_square :
    (intersectionNestedChainsIso U V).hom ≫
        singularChainsFunctor.map
          (TopCat.ofHom (nestedIntersectionInclusionContinuous U V)) =
      singularChainsFunctor.map
        (TopCat.ofHom (intersectionToRightContinuous U V)) := by
  dsimp [intersectionNestedChainsIso]
  rw [← Functor.map_comp]
  congr 1

/-- The induced isomorphism on integral singular homology. -/
noncomputable def intersectionNestedHomologyIso (n : ℕ) :
    (SingularChains (TopCat.of (U ∩ V : Set X))).homology n ≅
      (SingularChains (TopCat.of (nestedIntersection U V))).homology n :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).mapIso
    (intersectionNestedChainsIso U V)

/-- Homology-level naturality of the nested-intersection comparison. -/
theorem intersectionNested_homology_square (n : ℕ) :
    (intersectionNestedHomologyIso U V n).hom ≫
        HomologicalComplex.homologyMap
          (singularChainsFunctor.map
            (TopCat.ofHom (nestedIntersectionInclusionContinuous U V))) n =
      HomologicalComplex.homologyMap
        (singularChainsFunctor.map
          (TopCat.ofHom (intersectionToRightContinuous U V))) n := by
  change HomologicalComplex.homologyMap _ n ≫
      HomologicalComplex.homologyMap _ n = HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp,
    intersectionNested_chain_square]

/-- The direct relative cokernel for `(U ∩ V) → V` is canonically the
direct cokernel presentation of the topological pair
`(V, {x : V | x ∈ U})`. -/
noncomputable def intersectionNestedCokernelIso :
    cokernel (singularChainsFunctor.map
      (TopCat.ofHom (intersectionToRightContinuous U V))) ≅
      cokernel (singularSubspaceMap (nestedIntersection U V)) :=
  cokernel.mapIso
    (singularChainsFunctor.map
      (TopCat.ofHom (intersectionToRightContinuous U V)))
    (singularSubspaceMap (nestedIntersection U V))
    (intersectionNestedChainsIso U V) (Iso.refl _)
    (by
      dsimp only [singularSubspaceMap, subspaceInclusion,
        nestedIntersectionInclusionContinuous]
      simpa using (intersectionNested_chain_square U V).symm)

/-- The corresponding comparison with production relative singular chains. -/
noncomputable def intersectionNestedRelativeChainsIso :
    cokernel (singularChainsFunctor.map
      (TopCat.ofHom (intersectionToRightContinuous U V))) ≅
      RelativeSingularChains (nestedIntersection U V) :=
  intersectionNestedCokernelIso U V ≪≫
    (relativeSingularChainsIsoCokernelSubspaceMap
      (nestedIntersection U V)).symm

#print axioms intersectionNestedHomeomorph
#print axioms intersectionNested_chain_square
#print axioms intersectionNested_homology_square
#print axioms intersectionNestedRelativeChainsIso

end ConstructionTargets.NestedSubspaceIntersectionComparison
