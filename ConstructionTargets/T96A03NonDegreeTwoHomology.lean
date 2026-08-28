import ConstructionTargets.SphereEquatorGluingOpenCover
import ConstructionTargets.SphereHomology
import ConstructionTargets.T00A01MayerVietorisAdapters
import ConstructionTargets.MayerVietorisExactnessIsZero

/-!
# Homology away from degree two for an equator gluing

This file computes the parts of the integral homology of two 2-spheres glued
along an equator that do not use the degree-two extension calculation.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.T96A03NonDegreeTwoHomology

open ConstructionTargets.SphereEquatorGluingOpenCover
open ConstructionTargets.SphereHomology
open ConstructionTargets.T00A01MayerVietorisAdapters
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.IntegralSingularHomologyComparison
open ConstructionTargets.MayerVietorisExactnessIsZero
open ConstructionTargets.SingularHomologyConcrete
open T02A06

abbrev Gluing (h : sphereEquator 2 ≃ₜ sphereEquator 2) :=
  EquatorGluing 2 h

abbrev GroupH (h : sphereEquator 2 ≃ₜ sphereEquator 2) (k : ℕ) :=
  SingularHomology k (TopCat.of (Gluing h))

abbrev ModuleH (h : sphereEquator 2 ≃ₜ sphereEquator 2) (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Gluing h)))

noncomputable def leftGroupHomologyIso (h : sphereEquator 2 ≃ₜ sphereEquator 2)
    (k : ℕ) :
    SingularHomology k (TopCat.of (leftOpen 2 h)) ≅ GroupHomology 2 k :=
  singularHomologyIsoOfHomotopyEquiv (leftPieceHomotopyEquiv 2 h) k

noncomputable def rightGroupHomologyIso (h : sphereEquator 2 ≃ₜ sphereEquator 2)
    (k : ℕ) :
    SingularHomology k (TopCat.of (rightOpen 2 h)) ≅ GroupHomology 2 k :=
  singularHomologyIsoOfHomotopyEquiv (rightPieceHomotopyEquiv 2 h) k

noncomputable def intersectionGroupHomologyIso
    (h : sphereEquator 2 ≃ₜ sphereEquator 2) (k : ℕ) :
    SingularHomology k (TopCat.of (leftOpen 2 h ∩ rightOpen 2 h : Set (Gluing h))) ≅
      GroupHomology 1 k :=
  singularHomologyIsoOfHomotopyEquiv (intersectionPieceHomotopyEquiv 2 h) k ≪≫
    singularHomologyIsoOfHomotopyEquiv
      (sphereHomeomorphEquator 2).symm.toHomotopyEquiv k

noncomputable def leftH0IsoInt (h : sphereEquator 2 ≃ₜ sphereEquator 2) :
    SingularHomology 0 (TopCat.of (leftOpen 2 h)) ≅ AddCommGrpCat.of ℤ :=
  leftGroupHomologyIso h 0 ≪≫ sphereH0IsoInt 2 (by omega)

noncomputable def rightH0IsoInt (h : sphereEquator 2 ≃ₜ sphereEquator 2) :
    SingularHomology 0 (TopCat.of (rightOpen 2 h)) ≅ AddCommGrpCat.of ℤ :=
  rightGroupHomologyIso h 0 ≪≫ sphereH0IsoInt 2 (by omega)

noncomputable def intersectionH0IsoInt
    (h : sphereEquator 2 ≃ₜ sphereEquator 2) :
    SingularHomology 0
      (TopCat.of (leftOpen 2 h ∩ rightOpen 2 h : Set (Gluing h))) ≅
      AddCommGrpCat.of ℤ :=
  intersectionGroupHomologyIso h 0 ≪≫ sphereH0IsoInt 1 (by omega)

noncomputable def gluingGroupH0IsoInt
    (h : sphereEquator 2 ≃ₜ sphereEquator 2) :
    GroupH h 0 ≅ AddCommGrpCat.of ℤ := by
  letI : Nonempty (leftOpen 2 h) :=
    ⟨leftSphereInclusion 2 h (Classical.choice (euclideanUnitSphere_nonempty (by omega)))⟩
  letI : Nonempty (rightOpen 2 h) :=
    ⟨rightSphereInclusion 2 h (Classical.choice (euclideanUnitSphere_nonempty (by omega)))⟩
  letI : Nonempty (leftOpen 2 h ∩ rightOpen 2 h : Set (Gluing h)) :=
    ⟨equatorIntersectionInclusion 2 h (Classical.choice inferInstance)⟩
  exact openCoverH0IsoOfCoordinates
    (leftOpen 2 h) (rightOpen 2 h)
    (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h)
    (leftOpen_union_rightOpen 2 h)
    (intersectionH0IsoInt h) (leftH0IsoInt h) (rightH0IsoInt h)

noncomputable def gluingModuleH0IsoInt
    (h : sphereEquator 2 ≃ₜ sphereEquator 2) :
    ModuleH h 0 ≅ ModuleCat.of ℤ ℤ :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of (Gluing h)) 0
    (ModuleCat.of ℤ ℤ) (gluingGroupH0IsoInt h)

theorem leftGroupH1_isZero (h : sphereEquator 2 ≃ₜ sphereEquator 2) :
    IsZero (SingularHomology 1 (TopCat.of (leftOpen 2 h))) :=
  (spherePositiveHomology_isZero_of_lt 2 1 (by omega) (by omega)).of_iso
    (leftGroupHomologyIso h 1)

theorem rightGroupH1_isZero (h : sphereEquator 2 ≃ₜ sphereEquator 2) :
    IsZero (SingularHomology 1 (TopCat.of (rightOpen 2 h))) :=
  (spherePositiveHomology_isZero_of_lt 2 1 (by omega) (by omega)).of_iso
    (rightGroupHomologyIso h 1)

theorem gluingGroupH1_isZero (h : sphereEquator 2 ≃ₜ sphereEquator 2) :
    IsZero (GroupH h 1) := by
  letI : Nonempty (leftOpen 2 h) :=
    ⟨leftSphereInclusion 2 h (Classical.choice (euclideanUnitSphere_nonempty (by omega)))⟩
  letI : Nonempty (leftOpen 2 h ∩ rightOpen 2 h : Set (Gluing h)) :=
    ⟨equatorIntersectionInclusion 2 h (Classical.choice inferInstance)⟩
  letI : Mono (productionIntersectionArrow (leftOpen 2 h) (rightOpen 2 h) 0) :=
    productionIntersectionArrow_mono_zero_of_coordinates
      (leftOpen 2 h) (rightOpen 2 h) (intersectionH0IsoInt h) (leftH0IsoInt h)
  apply isZero_middle_of_two_exact_of_isZero_left_of_mono_right
    (productionReassemblyArrow (leftOpen 2 h) (rightOpen 2 h) 1)
    (productionConnecting (leftOpen 2 h) (rightOpen 2 h)
      (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h)
      (leftOpen_union_rightOpen 2 h) 0)
    (productionIntersectionArrow (leftOpen 2 h) (rightOpen 2 h) 0)
    _ _
    (productionMayerVietoris_exact_union
      (leftOpen 2 h) (rightOpen 2 h)
      (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h)
      (leftOpen_union_rightOpen 2 h) 0)
    (productionMayerVietoris_exact_intersection
      (leftOpen 2 h) (rightOpen 2 h)
      (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h)
      (leftOpen_union_rightOpen 2 h) 0)
    ((biprod_isZero_iff _ _).mpr ⟨leftGroupH1_isZero h, rightGroupH1_isZero h⟩)

theorem gluingModuleH1_isZero (h : sphereEquator 2 ≃ₜ sphereEquator 2) :
    IsZero (ModuleH h 1) :=
  singularHomologyModuleIsZeroOfGroupIsZero (TopCat.of (Gluing h)) 1
    (gluingGroupH1_isZero h)

theorem leftGroupHomology_isZero_of_gt_two
    (h : sphereEquator 2 ≃ₜ sphereEquator 2) (k : ℕ) (hk : 2 < k) :
    IsZero (SingularHomology k (TopCat.of (leftOpen 2 h))) :=
  (sphereHomology_isZero_of_gt 2 k hk).of_iso (leftGroupHomologyIso h k)

theorem rightGroupHomology_isZero_of_gt_two
    (h : sphereEquator 2 ≃ₜ sphereEquator 2) (k : ℕ) (hk : 2 < k) :
    IsZero (SingularHomology k (TopCat.of (rightOpen 2 h))) :=
  (sphereHomology_isZero_of_gt 2 k hk).of_iso (rightGroupHomologyIso h k)

theorem intersectionGroupHomology_isZero_of_gt_one
    (h : sphereEquator 2 ≃ₜ sphereEquator 2) (k : ℕ) (hk : 1 < k) :
    IsZero (SingularHomology k
      (TopCat.of (leftOpen 2 h ∩ rightOpen 2 h : Set (Gluing h)))) :=
  (sphereHomology_isZero_of_gt 1 k hk).of_iso
    (intersectionGroupHomologyIso h k)

theorem gluingGroupHomology_isZero_of_gt_two
    (h : sphereEquator 2 ≃ₜ sphereEquator 2) (k : ℕ) (hk : 2 < k) :
    IsZero (GroupH h k) := by
  cases k with
  | zero => omega
  | succ n =>
      let hex := productionMayerVietoris_exact_union
        (leftOpen 2 h) (rightOpen 2 h)
        (leftOpen_isOpen 2 h) (rightOpen_isOpen 2 h)
        (leftOpen_union_rightOpen 2 h) n
      apply hex.isZero_X₂
      · exact (biprod_isZero_iff _ _).mpr
          ⟨leftGroupHomology_isZero_of_gt_two h (n + 1) (by omega),
            rightGroupHomology_isZero_of_gt_two h (n + 1) (by omega)⟩ |>.eq_of_src _ _
      · exact (intersectionGroupHomology_isZero_of_gt_one h n (by omega)).eq_of_tgt _ _

theorem gluingModuleHomology_isZero_of_gt_two
    (h : sphereEquator 2 ≃ₜ sphereEquator 2) (k : ℕ) (hk : 2 < k) :
    IsZero (ModuleH h k) :=
  singularHomologyModuleIsZeroOfGroupIsZero (TopCat.of (Gluing h)) k
    (gluingGroupHomology_isZero_of_gt_two h k hk)

theorem nonDegreeTwoIntegralHomology
    (h : sphereEquator 2 ≃ₜ sphereEquator 2) :
    Nonempty (ModuleH h 0 ≅ ModuleCat.of ℤ ℤ) ∧
      IsZero (ModuleH h 1) ∧
      ∀ k : ℕ, 2 < k → IsZero (ModuleH h k) :=
  ⟨⟨gluingModuleH0IsoInt h⟩, gluingModuleH1_isZero h,
    gluingModuleHomology_isZero_of_gt_two h⟩

#print axioms gluingModuleH0IsoInt
#print axioms gluingModuleH1_isZero
#print axioms gluingModuleHomology_isZero_of_gt_two
#print axioms nonDegreeTwoIntegralHomology

end ConstructionTargets.T96A03NonDegreeTwoHomology
