import ConstructionTargets.CoefficientRadialPair
import ConstructionTargets.T02A06SphereShift
noncomputable section
namespace ConstructionTargets.CoefficientSphereShift
open CategoryTheory CategoryTheory.Limits
open T02A06 T02A06HemisphereExcision T02A06DiskRadialComparison
open CoefficientRadialPair
variable (R : Type) [CommRing R]

def coordinateMap (n : ℕ) := pairMap R (puncturedOpenDiskSet n)
  (puncturedUpperHemisphere n) (openDiskToOpenUpperMap n) (openDiskToOpenUpperMap_mapsTo n)

theorem coordinate_projection (n j : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (puncturedOpenDiskSet n))).f j ≫
      (coordinateMap R n).f j =
    (absoluteMap R (openDiskToOpenUpperMap n)).f j ≫
      (cokernel.π (CoefficientRelativeSmall.subspaceMap R (puncturedUpperHemisphere n))).f j :=
  projection_degree R _ _ _ _ j

theorem coordinate_absolute_isIso (n j : ℕ) :
    IsIso (HomologicalComplex.homologyMap (absoluteMap R (openDiskToOpenUpperMap n)) j) := by
  let e : TopCat.of (euclideanOpenDisk n) ≅ TopCat.of (openUpperHemisphere n) :=
    TopCat.isoOfHomeo (openDiskHomeomorphOpenUpper n)
  change IsIso ((F R j).map e.hom)
  infer_instance

theorem coordinate_subspace_isIso (n j : ℕ) :
    IsIso (HomologicalComplex.homologyMap (subMap R (puncturedOpenDiskSet n)
      (puncturedUpperHemisphere n) (openDiskToOpenUpperMap n) (openDiskToOpenUpperMap_mapsTo n)) j) := by
  let e : TopCat.of (puncturedOpenDiskSet n) ≅ TopCat.of (puncturedUpperHemisphere n) :=
    TopCat.isoOfHomeo (puncturedOpenDiskHomeomorphPuncturedUpper n)
  change IsIso ((F R j).map e.hom)
  infer_instance

def coordinateIso (n j : ℕ) :
    (CoefficientRelativeSmall.relativeChains R (puncturedOpenDiskSet n)).homology j ≅
    (CoefficientRelativeSmall.relativeChains R (puncturedUpperHemisphere n)).homology j := by
  letI : Mono (CoefficientRelativeSmall.subspaceMap R (puncturedOpenDiskSet n)) :=
    CoefficientRelativeSmall.subspaceMap_mono R _
  letI : Mono (CoefficientRelativeSmall.subspaceMap R (puncturedUpperHemisphere n)) :=
    CoefficientRelativeSmall.subspaceMap_mono R _
  exact CoefficientCokernelComparison.comparisonIso R
    (CoefficientRelativeSmall.subspaceMap R (puncturedOpenDiskSet n))
    (CoefficientRelativeSmall.subspaceMap R (puncturedUpperHemisphere n)) _ _
    (square R _ _ _ (openDiskToOpenUpperMap_mapsTo n))
    (coordinate_subspace_isIso R n) (coordinate_absolute_isIso R n) j

theorem coordinateIso_hom (n j : ℕ) : (coordinateIso R n j).hom =
    HomologicalComplex.homologyMap (coordinateMap R n) j := rfl

def hemisphereIso (n j : ℕ) := CoefficientExcision.homologyIso R
  (northPoleComplement n) (closedLowerHemisphere n)
  (closedLowerHemisphere_isClosed n)
  (closedLowerHemisphere_subset_interior_northPoleComplement n) j

theorem hemisphereIso_hom (n j : ℕ) : (hemisphereIso R n j).hom =
    HomologicalComplex.homologyMap (CoefficientExcision.excisionMap R
      (northPoleComplement n) (closedLowerHemisphere n)) j :=
  CoefficientExcision.homologyIso_hom R _ _ _ _ j

theorem hemisphere_projection (n j : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R
      (SingularExcision.excisedSubspace (northPoleComplement n) (closedLowerHemisphere n)))).f j ≫
    (CoefficientExcision.excisionMap R (northPoleComplement n) (closedLowerHemisphere n)).f j =
    (CoefficientRelativeSmall.subspaceMap R ((closedLowerHemisphere n)ᶜ)).f j ≫
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (northPoleComplement n))).f j :=
  CoefficientExcision.projection_degree R _ _ j

theorem coordinate_inverse_left (n j : ℕ) : (coordinateIso R n j).inv ≫
    HomologicalComplex.homologyMap (coordinateMap R n) j = 𝟙 _ :=
  (coordinateIso R n j).inv_hom_id

theorem coordinate_inverse_right (n j : ℕ) :
    HomologicalComplex.homologyMap (coordinateMap R n) j ≫ (coordinateIso R n j).inv = 𝟙 _ :=
  (coordinateIso R n j).hom_inv_id

def sphereToDiskIso (n q : ℕ) (hq : q ≠ 0) :
    CoefficientContractiblePair.H R q (TopCat.of (ambientSphere n)) ≅
    (CoefficientRelativeSmall.relativeChains R (closedDiskBoundarySet n)).homology q :=
  CoefficientContractiblePair.projectionIso R (northPoleComplement n) q hq ≪≫
    (hemisphereIso R n q).symm ≪≫ (coordinateIso R n q).symm ≪≫ (radialIso R n q).symm

theorem sphereToDiskIso_hom (n q : ℕ) (hq : q ≠ 0) :
    (sphereToDiskIso R n q hq).hom =
    HomologicalComplex.homologyMap (CoefficientPairSequence.projection R (northPoleComplement n)) q ≫
    (hemisphereIso R n q).inv ≫ (coordinateIso R n q).inv ≫ (radialIso R n q).inv := rfl

local instance diskContractible (n : ℕ) : ContractibleSpace (euclideanClosedDisk n) :=
  Metric.contractibleSpace_closedBall (by norm_num)

def boundaryIso (n k : ℕ) (hk : k ≠ 0) :
    (CoefficientRelativeSmall.relativeChains R (closedDiskBoundarySet n)).homology (k+1) ≅
    CoefficientContractiblePair.H R k (TopCat.of (euclideanUnitSphere n)) :=
  CoefficientContractiblePair.contractibleConnectingIso R (closedDiskBoundarySet n) k hk ≪≫
    (F R k).mapIso (TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph n))

def sphereShift (n k : ℕ) (hk : k ≠ 0) :
    CoefficientContractiblePair.H R (k+1) (TopCat.of (ambientSphere n)) ≅
    CoefficientContractiblePair.H R k (TopCat.of (euclideanUnitSphere n)) :=
  sphereToDiskIso R n (k+1) (by omega) ≪≫ boundaryIso R n k hk

theorem sphereShift_hom (n k : ℕ) (hk : k ≠ 0) :
    (sphereShift R n k hk).hom =
    (sphereToDiskIso R n (k+1) (by omega)).hom ≫
    CoefficientPairSequence.connecting R (closedDiskBoundarySet n) k ≫
    (F R k).map (TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph n)).hom := rfl

def sphereH1KernelIso (n : ℕ) :
    CoefficientContractiblePair.H R 1 (TopCat.of (ambientSphere n)) ≅
    kernel (HomologicalComplex.homologyMap
      (CoefficientRelativeSmall.subspaceMap R (closedDiskBoundarySet n)) 0) :=
  sphereToDiskIso R n 1 (by decide) ≪≫
    CoefficientContractiblePair.contractibleH1KernelIso R (closedDiskBoundarySet n)

theorem sphereH1KernelIso_hom (n : ℕ) : (sphereH1KernelIso R n).hom =
    (sphereToDiskIso R n 1 (by decide)).hom ≫
      (CoefficientContractiblePair.contractibleH1KernelIso R (closedDiskBoundarySet n)).hom := rfl

theorem sphereH1Kernel_projection (n : ℕ) :
    (sphereH1KernelIso R n).hom ≫ kernel.ι (HomologicalComplex.homologyMap
      (CoefficientRelativeSmall.subspaceMap R (closedDiskBoundarySet n)) 0) =
    (sphereToDiskIso R n 1 (by decide)).hom ≫
      CoefficientPairSequence.connecting R (closedDiskBoundarySet n) 0 := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc, CoefficientContractiblePair.contractibleH1Kernel_projection]

theorem shift_inverse_left (n k : ℕ) (hk : k ≠ 0) :
    (sphereShift R n k hk).inv ≫ (sphereShift R n k hk).hom = 𝟙 _ :=
  (sphereShift R n k hk).inv_hom_id

theorem shift_inverse_right (n k : ℕ) (hk : k ≠ 0) :
    (sphereShift R n k hk).hom ≫ (sphereShift R n k hk).inv = 𝟙 _ :=
  (sphereShift R n k hk).hom_inv_id

theorem kernel_inverse_left (n : ℕ) :
    (sphereH1KernelIso R n).inv ≫ (sphereH1KernelIso R n).hom = 𝟙 _ :=
  (sphereH1KernelIso R n).inv_hom_id

theorem kernel_inverse_right (n : ℕ) :
    (sphereH1KernelIso R n).hom ≫ (sphereH1KernelIso R n).inv = 𝟙 _ :=
  (sphereH1KernelIso R n).hom_inv_id

def integral_shift (n k : ℕ) (hk : k ≠ 0) := sphereShift ℤ n k hk
def rational_shift (n k : ℕ) (hk : k ≠ 0) := sphereShift ℚ n k hk
def integral_kernel (n : ℕ) := sphereH1KernelIso ℤ n
def rational_kernel (n : ℕ) := sphereH1KernelIso ℚ n
#print axioms hemisphereIso_hom
#print axioms hemisphere_projection
#print axioms coordinate_inverse_left
#print axioms coordinate_inverse_right
#print axioms sphereH1KernelIso_hom
#print axioms coordinate_projection
#print axioms coordinateIso_hom
#print axioms sphereToDiskIso_hom
#print axioms sphereShift_hom
#print axioms sphereH1Kernel_projection
#print axioms shift_inverse_left
#print axioms shift_inverse_right
#print axioms kernel_inverse_left
#print axioms kernel_inverse_right
#print axioms integral_shift
#print axioms rational_shift
#print axioms integral_kernel
#print axioms rational_kernel
end ConstructionTargets.CoefficientSphereShift
