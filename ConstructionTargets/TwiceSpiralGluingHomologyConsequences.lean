import ConstructionTargets.TwiceSpiralGluingHomology

/-!
# Homology consequences of the twice-spiral production arrow

This file transports the computed monicity and cokernel of the literal
twice-spiral arrow through the production Mayer--Vietoris sequence.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.TwiceSpiralGluingHomologyConsequences

open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.SolidTorusHomotopyAndHomology
open ConstructionTargets.TwiceSpiralH1Coordinates
open ConstructionTargets.TwiceSpiralSignedArrowAlgebra
open ConstructionTargets.TwiceSpiralGluingHomology
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.BooleanTwoCoverScaffold
open ConstructionTargets.T00A01MayerVietorisAdapters
open ConstructionTargets.IntegralSingularHomologyComparison

private abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  SingularHomology k (TopCat.of X)

/-- Cokernels are invariant under conjugating both objects by isomorphisms. -/
noncomputable def cokernelIsoOfConjugation
    {A B A' B' : AddCommGrpCat} (f : A ⟶ B) (f' : A' ⟶ B')
    (eA : A ≅ A') (eB : B ≅ B') (w : f ≫ eB.hom = eA.hom ≫ f') :
    cokernel f ≅ cokernel f' where
  hom := cokernel.map f f' eA.hom eB.hom w
  inv := cokernel.map f' f eA.inv eB.inv (by
    simpa [Category.assoc]
      using congrArg (fun q ↦ eA.inv ≫ q ≫ eB.inv) w.symm)
  hom_inv_id := by
    apply (cancel_epi (cokernel.π f)).1
    simp [cokernel.map, Category.assoc]
  inv_hom_id := by
    apply (cancel_epi (cokernel.π f')).1
    simp [cokernel.map, Category.assoc]

variable (h : BoundaryTorus ≃ₜ BoundaryTorus) (z₀ : BoundaryTorus)
variable (e₁ : FundamentalGroup BoundaryTorus z₀ ≃* Multiplicative (ℤ × ℤ))
variable (e₂ : FundamentalGroup BoundaryTorus (h z₀) ≃* Multiplicative (ℤ × ℤ))
variable (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z₀) ≃* Multiplicative ℤ)
variable (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z₀)) ≃* Multiplicative ℤ)
variable (hinc₁ : ∀ p, c₁ (FundamentalGroup.map
  ⟨boundaryInclusion, continuous_boundaryInclusion⟩ z₀ p) =
    secondCoordinateHom (e₁ p))
variable (hinc₂ : ∀ p, c₂ (FundamentalGroup.map
  ⟨boundaryInclusion, continuous_boundaryInclusion⟩ (h z₀) p) =
    secondCoordinateHom (e₂ p))
variable (h10 : boundaryCoordinateMap h z₀ e₁ e₂
  (Multiplicative.ofAdd (1, 0)) = Multiplicative.ofAdd (1, 2))

private abbrev d : ℤ := twiceSpiralSecondCoefficient h z₀ e₁ e₂

private noncomputable def piecesH1ProductCoordinate :
    H 1 (leftOpen h) ⊞ H 1 (rightOpen h) ≅ IntPairGroup :=
  piecesH1Coordinate h z₀ c₁ c₂ ≪≫
    AddCommGrpCat.biprodIsoProd (AddCommGrpCat.of ℤ) (AddCommGrpCat.of ℤ)

include hinc₁ hinc₂ h10 in
theorem productionH1CoordinateArrow_product_eq :
    productionH1CoordinateArrow h z₀ e₁ c₁ c₂ ≫
        (AddCommGrpCat.biprodIsoProd (AddCommGrpCat.of ℤ)
          (AddCommGrpCat.of ℤ)).hom =
      twiceSpiralSignedArrow (d h z₀ e₁ e₂) :=
  productionH1ArrowComparison h z₀ e₁ e₂ c₁ c₂ hinc₁ hinc₂ h10

include hinc₁ hinc₂ h10 in
theorem productionH1_conjugation_square :
    productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫
        (piecesH1ProductCoordinate h z₀ c₁ c₂).hom =
      (intersectionH1Coordinate h z₀ e₁).hom ≫
        twiceSpiralSignedArrow (d h z₀ e₁ e₂) := by
  have hc := congrArg (fun q ↦
      (intersectionH1Coordinate h z₀ e₁).hom ≫ q)
    (productionH1CoordinateArrow_product_eq h z₀ e₁ e₂ c₁ c₂
      hinc₁ hinc₂ h10)
  simpa only [productionH1CoordinateArrow, piecesH1ProductCoordinate,
    Category.assoc, Iso.hom_inv_id_assoc] using hc

include hinc₁ hinc₂ h10 in
theorem productionH1CoordinateArrow_product_mono : Mono
    (productionH1CoordinateArrow h z₀ e₁ c₁ c₂ ≫
      (AddCommGrpCat.biprodIsoProd (AddCommGrpCat.of ℤ)
        (AddCommGrpCat.of ℤ)).hom) := by
  rw [productionH1CoordinateArrow_product_eq h z₀ e₁ e₂ c₁ c₂ hinc₁ hinc₂ h10]
  infer_instance

include hinc₁ hinc₂ h10 in
theorem productionIntersectionArrow_H1_mono : Mono
    (productionIntersectionArrow (leftOpen h) (rightOpen h) 1) := by
  let eI := intersectionH1Coordinate h z₀ e₁
  let eP := piecesH1ProductCoordinate h z₀ c₁ c₂
  have hm : Mono (eI.inv ≫
      productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫ eP.hom) := by
    change Mono (productionH1CoordinateArrow h z₀ e₁ c₁ c₂ ≫
      (AddCommGrpCat.biprodIsoProd (AddCommGrpCat.of ℤ)
        (AddCommGrpCat.of ℤ)).hom)
    exact productionH1CoordinateArrow_product_mono h z₀ e₁ e₂ c₁ c₂
      hinc₁ hinc₂ h10
  haveI : Mono (productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫
      eP.hom) := by
    rw [show productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫ eP.hom =
      eI.hom ≫ (eI.inv ≫
        productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫ eP.hom) by
          simp]
    infer_instance
  exact mono_of_mono_fac
    (g := productionIntersectionArrow (leftOpen h) (rightOpen h) 1)
    (f := eP.hom)
    (h := productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫ eP.hom)
    (by rfl)

theorem piecesH2_isZero : IsZero
    (H 2 (leftOpen h) ⊞ H 2 (rightOpen h)) := by
  rw [biprod_isZero_iff]
  constructor
  · exact (groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of SolidTorus) 2
      (solidTorusHomology_isZero_of_one_lt 2 (by omega))).of_iso
        (singularHomologyIsoOfHomotopyEquiv (leftPieceHomotopyEquiv h) 2)
  · exact (groupHomologyIsZeroOfModuleHomologyIsZero (TopCat.of SolidTorus) 2
      (solidTorusHomology_isZero_of_one_lt 2 (by omega))).of_iso
        (singularHomologyIsoOfHomotopyEquiv (rightPieceHomotopyEquiv h) 2)

instance productionConnecting_H1_mono : Mono
    (productionConnecting (leftOpen h) (rightOpen h)
      (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h) 1) := by
  exact (productionMayerVietoris_exact_union (leftOpen h) (rightOpen h)
    (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h) 1).mono_g
      ((piecesH2_isZero h).eq_of_src _ _)

include hinc₁ hinc₂ h10 in
theorem productionConnecting_H1_eq_zero :
    productionConnecting (leftOpen h) (rightOpen h)
      (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h) 1 = 0 := by
  letI : Mono (productionIntersectionArrow (leftOpen h) (rightOpen h) 1) :=
    productionIntersectionArrow_H1_mono h z₀ e₁ e₂ c₁ c₂ hinc₁ hinc₂ h10
  exact (productionMayerVietoris_exact_intersection (leftOpen h) (rightOpen h)
    (leftOpen_isOpen h) (rightOpen_isOpen h)
    (leftOpen_union_rightOpen h) 1).mono_g_iff.mp inferInstance

include hinc₁ hinc₂ h10 in
theorem gluingH2_isZero : IsZero (H 2 (Gluing h)) := by
  let f := productionConnecting (leftOpen h) (rightOpen h)
    (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h) 1
  have hm : Mono f := by
    dsimp only [f]
    exact productionConnecting_H1_mono h
  have hf : f = 0 := by
    dsimp only [f]
    exact productionConnecting_H1_eq_zero h z₀ e₁ e₂ c₁ c₂ hinc₁ hinc₂ h10
  exact @IsZero.of_mono_eq_zero AddCommGrpCat _ _ _ _ f hm hf

instance productionReassemblyArrow_H1_epi : Epi
    (productionReassemblyArrow (leftOpen h) (rightOpen h) 1) := by
  letI : Nonempty (leftOpen h ∩ rightOpen h : Set (Gluing h)) :=
    ⟨boundaryIntersectionInclusion h (1,
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne 1)⟩
  letI : Nonempty (leftOpen h) := ⟨leftSolidTorusInclusion h (1, 0)⟩
  letI : Mono (productionIntersectionArrow (leftOpen h) (rightOpen h) 0) :=
    productionIntersectionArrow_mono_zero_of_coordinates
      (leftOpen h) (rightOpen h)
      (singularHomologyIsoOfHomotopyEquiv (intersectionPieceHomotopyEquiv h) 0 ≪≫
        ConstructionTargets.BoundaryTorusH0Cokernel.boundaryTorusH0GroupIsoInt)
      (singularHomologyIsoOfHomotopyEquiv (leftPieceHomotopyEquiv h) 0 ≪≫
        solidTorusH0GroupIsoInt)
  exact (productionMayerVietoris_exact_union (leftOpen h) (rightOpen h)
    (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h) 0).epi_f
      ((productionMayerVietoris_exact_intersection (leftOpen h) (rightOpen h)
        (leftOpen_isOpen h) (rightOpen_isOpen h)
        (leftOpen_union_rightOpen h) 0).mono_g_iff.mp inferInstance)

theorem productionH1_comp_reassembly :
    productionIntersectionArrow (leftOpen h) (rightOpen h) 1 ≫
      productionReassemblyArrow (leftOpen h) (rightOpen h) 1 = 0 := by
  rw [← booleanIntersectionArrow_eq_production (leftOpen h) (rightOpen h) 1,
    ← booleanReassemblyArrow_eq_production (leftOpen h) (rightOpen h)
      (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h) 1]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hz :
      HomologicalComplex.homologyMap
          (shortComplex (leftOpen h) (rightOpen h)).f 1 ≫
        HomologicalComplex.homologyMap
          (shortComplex (leftOpen h) (rightOpen h)).g 1 = 0 := by
    rw [← HomologicalComplex.homologyMap_comp,
      (shortComplex (leftOpen h) (rightOpen h)).zero,
      HomologicalComplex.homologyMap_zero]
  simpa only [Category.assoc, zero_comp, comp_zero] using
    congrArg (fun q ↦
      (booleanIntersectionProductionHomologyIso
          (leftOpen h) (rightOpen h) 1).inv ≫ q ≫
        (booleanUnionProductionHomologyIso (leftOpen h) (rightOpen h)
          (leftOpen_isOpen h) (rightOpen_isOpen h)
          (leftOpen_union_rightOpen h) 1).hom) hz

private noncomputable def productionH1PiecesShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk
    (productionIntersectionArrow (leftOpen h) (rightOpen h) 1)
    (productionReassemblyArrow (leftOpen h) (rightOpen h) 1)
    (productionH1_comp_reassembly h)

theorem productionH1PiecesShortComplex_exact :
    (productionH1PiecesShortComplex h).Exact := by
  exact productionMayerVietoris_exact_pieces (leftOpen h) (rightOpen h)
    (leftOpen_isOpen h) (rightOpen_isOpen h) (leftOpen_union_rightOpen h) 1

noncomputable def productionH1IsoCokernel :
    H 1 (Gluing h) ≅
      cokernel (productionIntersectionArrow (leftOpen h) (rightOpen h) 1) := by
  let S := productionH1PiecesShortComplex h
  letI : Epi S.g := by
    change Epi (productionReassemblyArrow (leftOpen h) (rightOpen h) 1)
    exact productionReassemblyArrow_H1_epi h
  let hR : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    (S.exact_and_epi_g_iff_g_is_cokernel.mp
      ⟨productionH1PiecesShortComplex_exact h, inferInstance⟩).some
  exact (IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel S.f) hR).symm

include hinc₁ hinc₂ h10 in
noncomputable def gluingH1GroupIsoZModTwo :
    H 1 (Gluing h) ≅ AddCommGrpCat.of (ZMod 2) :=
  productionH1IsoCokernel h ≪≫
    cokernelIsoOfConjugation
      (productionIntersectionArrow (leftOpen h) (rightOpen h) 1)
      (twiceSpiralSignedArrow (d h z₀ e₁ e₂))
      (intersectionH1Coordinate h z₀ e₁)
      (piecesH1ProductCoordinate h z₀ c₁ c₂)
      (productionH1_conjugation_square h z₀ e₁ e₂ c₁ c₂ hinc₁ hinc₂ h10) ≪≫
    twiceSpiralCokernelIso (d h z₀ e₁ e₂)

include hinc₁ hinc₂ h10 in
noncomputable def gluingH1ModuleIsoZModTwo :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Gluing h))) ≅
        ModuleCat.of ℤ (ZMod 2) :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of (Gluing h)) 1
    (ModuleCat.of ℤ (ZMod 2))
    (gluingH1GroupIsoZModTwo h z₀ e₁ e₂ c₁ c₂ hinc₁ hinc₂ h10)

include hinc₁ hinc₂ h10 in
theorem gluingH2Module_isZero : IsZero
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Gluing h))) := by
  exact singularHomologyModuleIsZeroOfGroupIsZero (TopCat.of (Gluing h)) 2
    (gluingH2_isZero h z₀ e₁ e₂ c₁ c₂ hinc₁ hinc₂ h10)

#print axioms productionIntersectionArrow_H1_mono
#print axioms gluingH2_isZero
#print axioms productionReassemblyArrow_H1_epi
#print axioms productionH1IsoCokernel
#print axioms cokernelIsoOfConjugation
#print axioms gluingH1GroupIsoZModTwo
#print axioms gluingH1ModuleIsoZModTwo
#print axioms gluingH2Module_isZero

end ConstructionTargets.TwiceSpiralGluingHomologyConsequences
