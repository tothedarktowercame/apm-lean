import ConstructionTargets.SolidTorusGluingOpenCover
import ConstructionTargets.CircleHomology
import ConstructionTargets.T00A01MayerVietorisAdapters

/-!
# Solid-torus deformation and integral homology

The closed disk factor is contracted explicitly.  Homology is then transported
through the resulting homotopy equivalence to the already computed circle;
no product or Kunneth theorem is used.
-/

open Set Topology CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap

noncomputable section

namespace ConstructionTargets.SolidTorusHomotopyAndHomology

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.CircleHomology
open ConstructionTargets.SphereHomology
open ConstructionTargets.T00A01MayerVietorisAdapters

def diskContractionVector (t : unitInterval) (x : Disk) : Plane :=
  (1 - (t : ℝ)) • x.1

theorem diskContractionVector_mem (t : unitInterval) (x : Disk) :
    diskContractionVector t x ∈ Metric.closedBall (0 : Plane) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, diskContractionVector, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.2.2)]
  have hx : ‖x.1‖ ≤ 1 := by
    simpa only [dist_zero_right] using (Metric.mem_closedBall.mp x.2)
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  nlinarith

def diskContraction (t : unitInterval) (x : Disk) : Disk :=
  ⟨diskContractionVector t x, diskContractionVector_mem t x⟩

theorem continuous_diskContraction :
    Continuous (fun p : unitInterval × Disk ↦ diskContraction p.1 p.2) := by
  apply Continuous.subtype_mk
  unfold diskContractionVector
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd))

@[simp] theorem diskContraction_zero (x : Disk) : diskContraction 0 x = x := by
  apply Subtype.ext
  simp [diskContraction, diskContractionVector]

@[simp] theorem diskContraction_one (x : Disk) :
    diskContraction 1 x = ⟨0, by simp⟩ := by
  apply Subtype.ext
  simp [diskContraction, diskContractionVector]

@[simp] theorem diskContraction_origin (t : unitInterval) :
    diskContraction t ⟨0, by simp⟩ = ⟨0, by simp⟩ := by
  apply Subtype.ext
  simp [diskContraction, diskContractionVector]

def solidTorusRetraction : C(SolidTorus, Circle) :=
  ⟨Prod.fst, continuous_fst⟩

def circleCoreInclusion : C(Circle, SolidTorus) :=
  ⟨fun z ↦ (z, ⟨0, by simp⟩), continuous_id.prodMk continuous_const⟩

def solidTorusContractionMap : C(unitInterval × SolidTorus, SolidTorus) :=
  ⟨fun p ↦ (p.2.1, diskContraction p.1 p.2.2), by
    exact continuous_fst.comp continuous_snd |>.prodMk
      (continuous_diskContraction.comp (continuous_fst.prodMk
        (continuous_snd.comp continuous_snd)))⟩

@[simp] theorem solidTorusContractionMap_zero (x : SolidTorus) :
    solidTorusContractionMap (0, x) = x := by
  simp [solidTorusContractionMap]

@[simp] theorem solidTorusContractionMap_one (x : SolidTorus) :
    solidTorusContractionMap (1, x) =
      circleCoreInclusion (solidTorusRetraction x) := by
  simp [solidTorusContractionMap, circleCoreInclusion, solidTorusRetraction]

@[simp] theorem solidTorusContractionMap_core (t : unitInterval) (z : Circle) :
    solidTorusContractionMap (t, circleCoreInclusion z) =
      circleCoreInclusion z := by
  simp [solidTorusContractionMap, circleCoreInclusion]

theorem solidTorusRetraction_comp_circleCoreInclusion :
    solidTorusRetraction.comp circleCoreInclusion = ContinuousMap.id Circle := by
  ext
  rfl

def solidTorusContraction : ContinuousMap.Homotopy
    (ContinuousMap.id SolidTorus)
    (circleCoreInclusion.comp solidTorusRetraction) where
  toFun := solidTorusContractionMap
  continuous_toFun := solidTorusContractionMap.continuous
  map_zero_left := solidTorusContractionMap_zero
  map_one_left := solidTorusContractionMap_one

def solidTorusHomotopyEquivCircle : SolidTorus ≃ₕ Circle where
  toFun := solidTorusRetraction
  invFun := circleCoreInclusion
  left_inv := ⟨solidTorusContraction.symm⟩
  right_inv := by rw [solidTorusRetraction_comp_circleCoreInclusion]

abbrev SolidTorusModuleHomology (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of SolidTorus))

noncomputable def solidTorusCircleModuleHomologyIso (k : ℕ) :
    SolidTorusModuleHomology k ≅
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle)) :=
  moduleHomologyIsoOfHomotopyEquiv solidTorusHomotopyEquivCircle k

noncomputable def circleH0IsoInt :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle)) ≅ ModuleCat.of ℤ ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
      (ModuleCat.of ℤ ℤ)).mapIso
        (TopCat.isoOfHomeo circleHomeomorphSphereOne) ≪≫
    sphereModuleH0IsoInt 1 one_pos

noncomputable def solidTorusH0IsoInt :
    SolidTorusModuleHomology 0 ≅ ModuleCat.of ℤ ℤ :=
  solidTorusCircleModuleHomologyIso 0 ≪≫ circleH0IsoInt

noncomputable def solidTorusH1IsoInt :
    SolidTorusModuleHomology 1 ≅ ModuleCat.of ℤ ℤ :=
  solidTorusCircleModuleHomologyIso 1 ≪≫
    ConstructionTargets.CircleHomology.circleH1IsoInt

theorem circleModuleHomology_isZero_of_one_lt (k : ℕ) (hk : 1 < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle)) := by
  have hs : IsZero (ModuleHomology 1 k) :=
    sphereModuleHomology_isZero_of_ne_zero_top 1 k (by omega) (by omega)
  exact hs.of_iso (((AlgebraicTopology.singularHomologyFunctor
    (ModuleCat ℤ) k).obj (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo circleHomeomorphSphereOne))

theorem solidTorusHomology_isZero_of_one_lt (k : ℕ) (hk : 1 < k) :
    IsZero (SolidTorusModuleHomology k) :=
  (circleModuleHomology_isZero_of_one_lt k hk).of_iso
    (solidTorusCircleModuleHomologyIso k)

#print axioms diskContractionVector_mem
#print axioms solidTorusHomotopyEquivCircle
#print axioms solidTorusH0IsoInt
#print axioms solidTorusH1IsoInt
#print axioms solidTorusHomology_isZero_of_one_lt

end ConstructionTargets.SolidTorusHomotopyAndHomology
