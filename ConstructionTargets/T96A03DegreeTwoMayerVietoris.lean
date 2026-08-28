import ConstructionTargets.ProjectiveQuotientExactSplitting
import ConstructionTargets.SphereEquatorGluingOpenCover
import ConstructionTargets.SphereHomology
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.T96A03DegreeTwoNormalization
import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# Degree-two Mayer--Vietoris calculation for the reusable equator gluing model

For two copies of `S²` glued along their equators, the degree-two part of the
production Mayer--Vietoris sequence is a short exact sequence

`0 ⟶ H₂(S²) ⊕ H₂(S²) ⟶ H₂(X) ⟶ H₁(S¹) ⟶ 0`.

This file derives monicity and epicity from the adjacent vanishing groups,
splits the sequence using projectivity of `ℤ`, and normalizes the resulting
three free coordinates.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ConstructionTargets.T96A03DegreeTwoMayerVietoris

open ConstructionTargets.IntegralSingularHomologyComparison
open ConstructionTargets.BooleanTwoCoverScaffold
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularExcision
open ProjectiveQuotientExactSplitting
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.SphereEquatorGluingOpenCover
open ConstructionTargets.SphereHomology
open ConstructionTargets.T00A01MayerVietorisAdapters
open ConstructionTargets.T96A03DegreeTwoNormalization
open T02A06

variable (h : sphereEquator 2 ≃ₜ sphereEquator 2)

abbrev X := EquatorGluing 2 h
abbrev U : Set (X h) := leftOpen 2 h
abbrev V : Set (X h) := rightOpen 2 h

abbrev H (k : ℕ) (Y : TopCat) := SingularHomology k Y

def hcover : U h ∪ V h = Set.univ := leftOpen_union_rightOpen 2 h

noncomputable def leftHomologyIsoSphere (k : ℕ) :
    H k (TopCat.of (U h)) ≅ GroupHomology 2 k :=
  singularHomologyIsoOfHomotopyEquiv (leftPieceHomotopyEquiv 2 h) k

noncomputable def rightHomologyIsoSphere (k : ℕ) :
    H k (TopCat.of (V h)) ≅ GroupHomology 2 k :=
  singularHomologyIsoOfHomotopyEquiv (rightPieceHomotopyEquiv 2 h) k

noncomputable def intersectionHomologyIsoSphere (k : ℕ) :
    H k (TopCat.of ↥(U h ∩ V h)) ≅ GroupHomology 1 k :=
  singularHomologyIsoOfHomotopyEquiv
    ((intersectionPieceHomotopyEquiv 2 h).trans
      (sphereHomeomorphEquator 2).symm.toHomotopyEquiv) k

theorem intersectionH2_isZero : IsZero (H 2 (TopCat.of ↥(U h ∩ V h))) :=
  (sphereHomology_isZero_of_gt 1 2 (by omega)).of_iso
    (intersectionHomologyIsoSphere h 2)

theorem leftH1_isZero : IsZero (H 1 (TopCat.of (U h))) :=
  (spherePositiveHomology_isZero_of_lt 2 1 (by omega) (by omega)).of_iso
    (leftHomologyIsoSphere h 1)

theorem rightH1_isZero : IsZero (H 1 (TopCat.of (V h))) :=
  (spherePositiveHomology_isZero_of_lt 2 1 (by omega) (by omega)).of_iso
    (rightHomologyIsoSphere h 1)

abbrev degreeTwoShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk
    (productionReassemblyArrow (U h) (V h) 2)
    (productionConnecting (U h) (V h)
      (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h) (hcover h) 1)
    (by
      rw [← booleanReassemblyArrow_eq_production (U h) (V h)
        (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h) (hcover h) 2]
      have hcancel :
          HomologicalComplex.homologyMap (shortComplex (U h) (V h)).g 2 ≫
              (booleanUnionProductionHomologyIso (U h) (V h)
                (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h) (hcover h) 2).hom ≫
              (booleanUnionProductionHomologyIso (U h) (V h)
                (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h) (hcover h) 2).inv ≫
              subcomplexMayerVietorisConnecting
                (leftRange (U h)) (rightRange (V h)) 1 =
            HomologicalComplex.homologyMap (shortComplex (U h) (V h)).g 2 ≫
              subcomplexMayerVietorisConnecting
                (leftRange (U h)) (rightRange (V h)) 1 := by simp
      have hz :
          HomologicalComplex.homologyMap (shortComplex (U h) (V h)).g 2 ≫
              subcomplexMayerVietorisConnecting
                (leftRange (U h)) (rightRange (V h)) 1 = 0 :=
        (subcomplexMayerVietorisShortComplex_shortExact
          (leftRange (U h)) (rightRange (V h))).comp_δ 2 1 rfl
      simp only [productionConnecting]
      calc
        _ = (booleanPiecesProductionHomologyIso (U h) (V h) 2).inv ≫
            (HomologicalComplex.homologyMap (shortComplex (U h) (V h)).g 2 ≫
              (booleanUnionProductionHomologyIso (U h) (V h)
                (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h) (hcover h) 2).hom ≫
              (booleanUnionProductionHomologyIso (U h) (V h)
                (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h) (hcover h) 2).inv ≫
              subcomplexMayerVietorisConnecting
                (leftRange (U h)) (rightRange (V h)) 1) ≫
            (booleanIntersectionProductionHomologyIso (U h) (V h) 1).hom := by
              simp only [Category.assoc]
        _ = (booleanPiecesProductionHomologyIso (U h) (V h) 2).inv ≫
            (HomologicalComplex.homologyMap (shortComplex (U h) (V h)).g 2 ≫
              subcomplexMayerVietorisConnecting
                (leftRange (U h)) (rightRange (V h)) 1) ≫
            (booleanIntersectionProductionHomologyIso (U h) (V h) 1).hom :=
              congrArg (fun k ↦
                (booleanPiecesProductionHomologyIso (U h) (V h) 2).inv ≫ k ≫
                  (booleanIntersectionProductionHomologyIso (U h) (V h) 1).hom)
                hcancel
        _ = 0 := by rw [hz]; simp)

theorem degreeTwo_exact : (degreeTwoShortComplex h).Exact :=
  productionMayerVietoris_exact_union
    (U h) (V h) (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h) (hcover h) 1

noncomputable instance degreeTwo_mono : Mono (degreeTwoShortComplex h).f := by
  apply (productionMayerVietoris_exact_pieces
    (U h) (V h) (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h) (hcover h) 2).mono_g_iff.mpr
  exact (intersectionH2_isZero h).eq_of_src _ _

noncomputable instance degreeTwo_epi : Epi (degreeTwoShortComplex h).g := by
  apply (productionMayerVietoris_exact_intersection
    (U h) (V h) (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h) (hcover h) 1).epi_f_iff.mpr
  exact ((biprod_isZero_iff _ _).mpr
    ⟨leftH1_isZero h, rightH1_isZero h⟩).eq_of_tgt _ _

theorem degreeTwo_shortExact : (degreeTwoShortComplex h).ShortExact where
  exact := degreeTwo_exact h
  mono_f := inferInstance
  epi_g := inferInstance

noncomputable def piecesH2IsoFinTwo :
    (degreeTwoShortComplex h).X₁ ≅ AddCommGrpCat.of (Fin 2 → ℤ) :=
  biprod.mapIso
      (leftHomologyIsoSphere h 2 ≪≫ sphereTopHomologyIsoInt 2 (by omega))
      (rightHomologyIsoSphere h 2 ≪≫ sphereTopHomologyIsoInt 2 (by omega)) ≪≫
    AddCommGrpCat.biprodIsoProd (AddCommGrpCat.of ℤ) (AddCommGrpCat.of ℤ) ≪≫
    (LinearEquiv.piFinTwo ℤ (fun _ : Fin 2 => ℤ)).symm.toAddEquiv.toAddCommGrpIso

noncomputable def quotientH1IsoInt :
    (degreeTwoShortComplex h).X₃ ≅ AddCommGrpCat.of ℤ :=
  intersectionHomologyIsoSphere h 1 ≪≫ sphereTopHomologyIsoInt 1 (by omega)

/-- The infinite cyclic additive group is projective: lift the image of `1`
through an epimorphism and extend it by integer multiples. -/
noncomputable instance intGroup_projective : Projective (AddCommGrpCat.of ℤ) where
  factors f e _ := by
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective e).mp inferInstance (f 1)
    refine ⟨AddCommGrpCat.ofHom (zmultiplesHom _ x), ?_⟩
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext_int
    simpa using hx

noncomputable def degreeTwoGroupIsoFinThree :
    (degreeTwoShortComplex h).X₂ ≅ AddCommGrpCat.of (Fin 3 → ℤ) := by
  letI : Projective (degreeTwoShortComplex h).X₃ :=
    Projective.of_iso (quotientH1IsoInt h).symm inferInstance
  exact shortExactIsoBiprod (degreeTwo_shortExact h) ≪≫
    biprod.mapIso (piecesH2IsoFinTwo h) (quotientH1IsoInt h) ≪≫
    AddCommGrpCat.biprodIsoProd
      (AddCommGrpCat.of (Fin 2 → ℤ)) (AddCommGrpCat.of ℤ) ≪≫
    forgetIntModules.mapIso finTwoProdIntModuleIso

/-- Module-category conclusion for the reusable gluing model. -/
noncomputable def degreeTwoModuleIsoFinThree :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (X h))) ≅
        ModuleCat.of ℤ (Fin 3 → ℤ) :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of (X h)) 2
    (ModuleCat.of ℤ (Fin 3 → ℤ)) (degreeTwoGroupIsoFinThree h)

end ConstructionTargets.T96A03DegreeTwoMayerVietoris
