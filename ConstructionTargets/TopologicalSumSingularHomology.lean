import ConstructionTargets.EmptyAndSumSingularHomology
import ConstructionTargets.T00A01MayerVietorisAdapters

/-!
# Integral singular homology of a topological sum

The two clopen summands form a production open cover.  Its empty intersection
turns the production reassembly arrow into an isomorphism in every degree.
-/

open Set Topology CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.TopologicalSumSingularHomology

open ConstructionTargets.EmptyAndSumSingularHomology
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.T00A01MayerVietorisAdapters
open ConstructionTargets.BooleanTwoCoverScaffold

private abbrev ssetChains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]

def leftSummand : Set (X ⊕ Y) := Set.range Sum.inl

def rightSummand : Set (X ⊕ Y) := Set.range Sum.inr

theorem leftSummand_isOpen : IsOpen (leftSummand X Y) := isOpen_range_inl

theorem rightSummand_isOpen : IsOpen (rightSummand X Y) := isOpen_range_inr

theorem leftSummand_union_rightSummand :
    leftSummand X Y ∪ rightSummand X Y = Set.univ := by
  ext z
  rcases z with x | y <;> simp [leftSummand, rightSummand]

noncomputable def leftSummandHomeomorph : leftSummand X Y ≃ₜ X :=
  Topology.IsEmbedding.inl.toHomeomorph.symm

noncomputable def rightSummandHomeomorph : rightSummand X Y ≃ₜ Y :=
  Topology.IsEmbedding.inr.toHomeomorph.symm

instance intersectionIsEmpty :
    IsEmpty (leftSummand X Y ∩ rightSummand X Y : Set (X ⊕ Y)) :=
  ⟨fun z => by
    rcases z with ⟨x | y, hx, hy⟩
    · rcases hy with ⟨y, h⟩
      contradiction
    · rcases hx with ⟨x, h⟩
      contradiction⟩

def intersectionHomeomorphEmpty :
    (leftSummand X Y ∩ rightSummand X Y : Set (X ⊕ Y)) ≃ₜ Empty where
  toFun z := isEmptyElim z
  invFun z := isEmptyElim z
  left_inv z := isEmptyElim z
  right_inv z := isEmptyElim z
  continuous_toFun := by
    rw [continuous_def]
    intro s hs
    convert isOpen_empty
    ext z
    exact isEmptyElim z
  continuous_invFun := by
    rw [continuous_def]
    intro s hs
    convert isOpen_empty
    ext z
    exact isEmptyElim z

abbrev H (k : ℕ) (Z : Type) [TopologicalSpace Z] :=
  SingularHomology k (TopCat.of Z)

noncomputable def leftSummandHomologyIso (k : ℕ) :
    H k (leftSummand X Y) ≅ H k X :=
  ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).mapIso (TopCat.isoOfHomeo (leftSummandHomeomorph X Y))

noncomputable def rightSummandHomologyIso (k : ℕ) :
    H k (rightSummand X Y) ≅ H k Y :=
  ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).mapIso (TopCat.isoOfHomeo (rightSummandHomeomorph X Y))

theorem intersectionHomology_isZero (k : ℕ) :
    IsZero (H k (leftSummand X Y ∩ rightSummand X Y : Set (X ⊕ Y))) :=
  (emptySingularHomology_isZero k).of_iso
    (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
      (AddCommGrpCat.of ℤ)).mapIso
        (TopCat.isoOfHomeo (intersectionHomeomorphEmpty X Y)))

noncomputable instance productionReassembly_isIso (k : ℕ) :
    IsIso (productionReassemblyArrow (leftSummand X Y) (rightSummand X Y) k) := by
  haveI : Mono
      (productionReassemblyArrow (leftSummand X Y) (rightSummand X Y) k) :=
    (productionMayerVietoris_exact_pieces
      (leftSummand X Y) (rightSummand X Y)
      (leftSummand_isOpen X Y) (rightSummand_isOpen X Y)
      (leftSummand_union_rightSummand X Y) k).mono_g_iff.mpr
        ((intersectionHomology_isZero X Y k).eq_of_src _ _)
  haveI : Epi
      (productionReassemblyArrow (leftSummand X Y) (rightSummand X Y) k) := by
    rcases k with _ | k
    · exact productionReassemblyArrow_epi_zero
        (leftSummand X Y) (rightSummand X Y)
        (leftSummand_isOpen X Y) (rightSummand_isOpen X Y)
        (leftSummand_union_rightSummand X Y)
    · exact (productionMayerVietoris_exact_union
        (leftSummand X Y) (rightSummand X Y)
        (leftSummand_isOpen X Y) (rightSummand_isOpen X Y)
        (leftSummand_union_rightSummand X Y) k).epi_f_iff.mpr
          ((intersectionHomology_isZero X Y k).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Integral singular homology sends a binary topological sum to the
categorical biproduct of the two homologies. -/
noncomputable def sumHomologyIsoBiprod (k : ℕ) :=
  (asIso (productionReassemblyArrow
      (leftSummand X Y) (rightSummand X Y) k)).symm ≪≫
    biprod.mapIso (leftSummandHomologyIso X Y k)
      (rightSummandHomologyIso X Y k)

/-- The canonical inclusion of the left summand. -/
def sumInl : TopCat.of X ⟶ TopCat.of (X ⊕ Y) :=
  TopCat.ofHom ⟨Sum.inl, continuous_inl⟩

/-- The canonical inclusion of the right summand. -/
def sumInr : TopCat.of Y ⟶ TopCat.of (X ⊕ Y) :=
  TopCat.ofHom ⟨Sum.inr, continuous_inr⟩

theorem leftHomeomorphInv_comp_subspaceInclusion :
    (TopCat.isoOfHomeo (leftSummandHomeomorph X Y) :
        TopCat.of (leftSummand X Y) ≅ TopCat.of X).inv ≫
        ConstructionTargets.SingularSubdivision.coverSubspaceInclusion
          (booleanCover (leftSummand X Y) (rightSummand X Y)) true =
      sumInl X Y := by
  rfl

theorem rightHomeomorphInv_comp_subspaceInclusion :
    (TopCat.isoOfHomeo (rightSummandHomeomorph X Y) :
        TopCat.of (rightSummand X Y) ≅ TopCat.of Y).inv ≫
        ConstructionTargets.SingularSubdivision.coverSubspaceInclusion
          (booleanCover (leftSummand X Y) (rightSummand X Y)) false =
      sumInr X Y := by
  rfl

theorem biprod_inl_comp_productionReassembly (k : ℕ) :
    biprod.inl ≫
        productionReassemblyArrow (leftSummand X Y) (rightSummand X Y) k =
      HomologicalComplex.homologyMap
        (ssetChains.map (TopCat.toSSet.map
          (ConstructionTargets.SingularSubdivision.coverSubspaceInclusion
            (booleanCover (leftSummand X Y) (rightSummand X Y)) true))) k := by
  unfold productionReassemblyArrow
  exact biprod.inl_desc _ _

theorem biprod_inr_comp_productionReassembly (k : ℕ) :
    biprod.inr ≫
        productionReassemblyArrow (leftSummand X Y) (rightSummand X Y) k =
      HomologicalComplex.homologyMap
        (ssetChains.map (TopCat.toSSet.map
          (ConstructionTargets.SingularSubdivision.coverSubspaceInclusion
            (booleanCover (leftSummand X Y) (rightSummand X Y)) false))) k := by
  unfold productionReassemblyArrow
  exact biprod.inr_desc _ _

theorem sumInl_homologyMap_comp_iso_hom (k : ℕ) :
    HomologicalComplex.homologyMap
        (ssetChains.map (TopCat.toSSet.map (sumInl X Y))) k ≫
      (sumHomologyIsoBiprod X Y k).hom = biprod.inl := by
  apply (Iso.comp_inv_eq (sumHomologyIsoBiprod X Y k).symm).2
  change HomologicalComplex.homologyMap
      (ssetChains.map (TopCat.toSSet.map (sumInl X Y))) k =
    biprod.inl ≫
      ((biprod.mapIso (leftSummandHomologyIso X Y k)
        (rightSummandHomologyIso X Y k)).inv ≫
      productionReassemblyArrow (leftSummand X Y) (rightSummand X Y) k)
  rw [biprod.mapIso_inv, biprod.inl_map_assoc]
  have hcomponent := congrArg
    (fun q ↦ (leftSummandHomologyIso X Y k).inv ≫ q)
    (biprod_inl_comp_productionReassembly X Y k)
  have hmap : HomologicalComplex.homologyMap
        (ssetChains.map (TopCat.toSSet.map (sumInl X Y))) k =
      (leftSummandHomologyIso X Y k).inv ≫
        HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map
            (ConstructionTargets.SingularSubdivision.coverSubspaceInclusion
              (booleanCover (leftSummand X Y) (rightSummand X Y)) true))) k := by
    change HomologicalComplex.homologyMap
        (ssetChains.map (TopCat.toSSet.map (sumInl X Y))) k =
      HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map
            ((TopCat.isoOfHomeo (leftSummandHomeomorph X Y) :
              TopCat.of (leftSummand X Y) ≅ TopCat.of X).inv))) k ≫
        HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map
            (ConstructionTargets.SingularSubdivision.coverSubspaceInclusion
              (booleanCover (leftSummand X Y) (rightSummand X Y)) true))) k
    let e := (TopCat.isoOfHomeo (leftSummandHomeomorph X Y) :
      TopCat.of (leftSummand X Y) ≅ TopCat.of X).inv
    let j := ConstructionTargets.SingularSubdivision.coverSubspaceInclusion
      (booleanCover (leftSummand X Y) (rightSummand X Y)) true
    calc
      _ = HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map (e ≫ j))) k := by
        exact congrArg (fun q ↦ HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map q)) k)
            (leftHomeomorphInv_comp_subspaceInclusion X Y).symm
      _ = HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map e) ≫
            ssetChains.map (TopCat.toSSet.map j)) k := by
        congr 1
        rw [Functor.map_comp, Functor.map_comp]
      _ = _ := HomologicalComplex.homologyMap_comp _ _ k
  exact hmap.trans (by simpa only [Category.assoc] using hcomponent.symm)

theorem sumInr_homologyMap_comp_iso_hom (k : ℕ) :
    HomologicalComplex.homologyMap
        (ssetChains.map (TopCat.toSSet.map (sumInr X Y))) k ≫
      (sumHomologyIsoBiprod X Y k).hom = biprod.inr := by
  apply (Iso.comp_inv_eq (sumHomologyIsoBiprod X Y k).symm).2
  change HomologicalComplex.homologyMap
      (ssetChains.map (TopCat.toSSet.map (sumInr X Y))) k =
    biprod.inr ≫
      ((biprod.mapIso (leftSummandHomologyIso X Y k)
        (rightSummandHomologyIso X Y k)).inv ≫
      productionReassemblyArrow (leftSummand X Y) (rightSummand X Y) k)
  rw [biprod.mapIso_inv, biprod.inr_map_assoc]
  have hcomponent := congrArg
    (fun q ↦ (rightSummandHomologyIso X Y k).inv ≫ q)
    (biprod_inr_comp_productionReassembly X Y k)
  have hmap : HomologicalComplex.homologyMap
        (ssetChains.map (TopCat.toSSet.map (sumInr X Y))) k =
      (rightSummandHomologyIso X Y k).inv ≫
        HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map
            (ConstructionTargets.SingularSubdivision.coverSubspaceInclusion
              (booleanCover (leftSummand X Y) (rightSummand X Y)) false))) k := by
    change HomologicalComplex.homologyMap
        (ssetChains.map (TopCat.toSSet.map (sumInr X Y))) k =
      HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map
            ((TopCat.isoOfHomeo (rightSummandHomeomorph X Y) :
              TopCat.of (rightSummand X Y) ≅ TopCat.of Y).inv))) k ≫
        HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map
            (ConstructionTargets.SingularSubdivision.coverSubspaceInclusion
              (booleanCover (leftSummand X Y) (rightSummand X Y)) false))) k
    let e := (TopCat.isoOfHomeo (rightSummandHomeomorph X Y) :
      TopCat.of (rightSummand X Y) ≅ TopCat.of Y).inv
    let j := ConstructionTargets.SingularSubdivision.coverSubspaceInclusion
      (booleanCover (leftSummand X Y) (rightSummand X Y)) false
    calc
      _ = HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map (e ≫ j))) k := by
        exact congrArg (fun q ↦ HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map q)) k)
            (rightHomeomorphInv_comp_subspaceInclusion X Y).symm
      _ = HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map e) ≫
            ssetChains.map (TopCat.toSSet.map j)) k := by
        congr 1
        rw [Functor.map_comp, Functor.map_comp]
      _ = _ := HomologicalComplex.homologyMap_comp _ _ k
  exact hmap.trans (by simpa only [Category.assoc] using hcomponent.symm)

theorem sumInl_homologyMap_eq_inl_comp_iso_inv (k : ℕ) :
    HomologicalComplex.homologyMap
        (ssetChains.map (TopCat.toSSet.map (sumInl X Y))) k =
      biprod.inl ≫ (sumHomologyIsoBiprod X Y k).inv :=
  (Iso.comp_inv_eq (sumHomologyIsoBiprod X Y k).symm).1
    (sumInl_homologyMap_comp_iso_hom X Y k)

theorem sumInr_homologyMap_eq_inr_comp_iso_inv (k : ℕ) :
    HomologicalComplex.homologyMap
        (ssetChains.map (TopCat.toSSet.map (sumInr X Y))) k =
      biprod.inr ≫ (sumHomologyIsoBiprod X Y k).inv :=
  (Iso.comp_inv_eq (sumHomologyIsoBiprod X Y k).symm).1
    (sumInr_homologyMap_comp_iso_hom X Y k)

/-- The inverse coordinate isomorphism is exactly descent along the two
canonical summand inclusions. -/
theorem sumHomologyIsoBiprod_inv_eq_desc (k : ℕ) :
    (sumHomologyIsoBiprod X Y k).inv =
      biprod.desc
        (HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map (sumInl X Y))) k)
        (HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map (sumInr X Y))) k) := by
  apply biprod.hom_ext'
  · calc
      _ = HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map (sumInl X Y))) k :=
        (sumInl_homologyMap_eq_inl_comp_iso_inv X Y k).symm
      _ = _ := (biprod.inl_desc _ _).symm
  · calc
      _ = HomologicalComplex.homologyMap
          (ssetChains.map (TopCat.toSSet.map (sumInr X Y))) k :=
        (sumInr_homologyMap_eq_inr_comp_iso_inv X Y k).symm
      _ = _ := (biprod.inr_desc _ _).symm

#print axioms leftSummand_union_rightSummand
#print axioms intersectionHomeomorphEmpty
#print axioms intersectionHomology_isZero
#print axioms productionReassembly_isIso
#print axioms sumHomologyIsoBiprod
#print axioms sumInl_homologyMap_comp_iso_hom
#print axioms sumInr_homologyMap_comp_iso_hom
#print axioms sumHomologyIsoBiprod_inv_eq_desc

end ConstructionTargets.TopologicalSumSingularHomology
