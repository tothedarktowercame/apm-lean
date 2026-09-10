import ConstructionTargets.CoefficientSphereShift
import ConstructionTargets.CoefficientH0
noncomputable section
namespace ConstructionTargets.CoefficientConnectedH0Map
open CategoryTheory CategoryTheory.Limits
open CoefficientH0
variable (R : Type) [CommRing R]
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [PathConnectedSpace X] [PathConnectedSpace Y]

def mapIso (x : X) (y : Y) :
    SingularHomology R 0 (TopCat.of X) ≅ SingularHomology R 0 (TopCat.of Y) :=
  h0Iso R x ≪≫ (h0Iso R y).symm

theorem mapIso_hom (f : C(X,Y)) (x : X) (y : Y) :
    (mapIso R x y).hom =
      HomologicalComplex.homologyMap (singularPostcomposition R f) 0 := by
  apply (cancel_mono (h0Iso R y).hom).mp
  change (h0Augmentation R ≫ singularVertexH0Class R y) ≫ h0Augmentation R = _
  rw [Category.assoc, singularVertexH0Class_comp_h0Augmentation, Category.comp_id]
  exact (h0Augmentation_naturality R f).symm

theorem normalized_map (f : C(X,Y)) (x : X) (y : Y) :
    (h0Iso R x).inv ≫ HomologicalComplex.homologyMap (singularPostcomposition R f) 0 ≫
      (h0Iso R y).hom = 𝟙 _ := by
  change singularVertexH0Class R x ≫
    (HomologicalComplex.homologyMap (singularPostcomposition R f) 0 ≫ h0Augmentation R) = 𝟙 _
  exact (congrArg (fun g => singularVertexH0Class R x ≫ g)
    (h0Augmentation_naturality R f)).trans
      (singularVertexH0Class_comp_h0Augmentation R x)

theorem map_isIso (f : C(X,Y)) :
    IsIso (HomologicalComplex.homologyMap (singularPostcomposition R f) 0) := by
  rw [← mapIso_hom R f (Classical.choice inferInstance) (Classical.choice inferInstance)]
  infer_instance

theorem inclusion_isIso (A : Set X) [PathConnectedSpace A] :
    IsIso (HomologicalComplex.homologyMap (CoefficientRelativeSmall.subspaceMap R A) 0) :=
  map_isIso R (⟨Subtype.val, continuous_subtype_val⟩ : C(A,X))

theorem inclusion_kernel_zero (A : Set X) [PathConnectedSpace A] :
    IsZero (kernel (HomologicalComplex.homologyMap (CoefficientRelativeSmall.subspaceMap R A) 0)) := by
  letI := inclusion_isIso R A
  rw [← Preadditive.mono_iff_isZero_kernel]
  infer_instance

open T02A06 T02A06DiskRadialComparison
local instance diskContractible : ContractibleSpace (euclideanClosedDisk 2) :=
  Metric.contractibleSpace_closedBall (by norm_num)
local instance spherePathConnected : PathConnectedSpace (euclideanUnitSphere 2) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (by rw [← Module.finrank_eq_rank']; norm_num) 0 (by norm_num))
local instance boundaryPathConnected : PathConnectedSpace (closedDiskBoundarySet 2) :=
  (closedDiskBoundaryHomeomorph 2).symm.surjective.pathConnectedSpace
    (closedDiskBoundaryHomeomorph 2).symm.continuous

theorem diskTwo_inclusion_isIso :
    IsIso (HomologicalComplex.homologyMap
      (CoefficientRelativeSmall.subspaceMap R (closedDiskBoundarySet 2)) 0) :=
  inclusion_isIso R _

theorem diskTwo_kernel_zero :
    IsZero (kernel (HomologicalComplex.homologyMap
      (CoefficientRelativeSmall.subspaceMap R (closedDiskBoundarySet 2)) 0)) :=
  inclusion_kernel_zero R _

theorem sphereTwo_H1_zero :
    IsZero (CoefficientContractiblePair.H R 1
      (TopCat.of (T02A06HemisphereExcision.ambientSphere 2))) :=
  (CoefficientSphereShift.sphereH1KernelIso R 2).isZero_iff.mpr (diskTwo_kernel_zero R)

def integral_sphereTwo_H1_zero := sphereTwo_H1_zero ℤ
def rational_sphereTwo_H1_zero := sphereTwo_H1_zero ℚ
#print axioms mapIso_hom
#print axioms normalized_map
#print axioms map_isIso
#print axioms inclusion_isIso
#print axioms inclusion_kernel_zero
#print axioms diskTwo_inclusion_isIso
#print axioms diskTwo_kernel_zero
#print axioms sphereTwo_H1_zero
#print axioms integral_sphereTwo_H1_zero
#print axioms rational_sphereTwo_H1_zero
end ConstructionTargets.CoefficientConnectedH0Map
