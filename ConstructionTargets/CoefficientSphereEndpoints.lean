import ConstructionTargets.CoefficientConnectedH0Map
import ConstructionTargets.CoefficientCodiagonalKernel
import ConstructionTargets.SphereZeroCoefficients
noncomputable section
namespace ConstructionTargets.CoefficientSphereEndpoints
open CategoryTheory CategoryTheory.Limits
open T02A06 T02A06DiskRadialComparison SingularHomologyConcrete
variable (R : Type) [CommRing R]
abbrev F := CoefficientRadialPair.F R 0
abbrev boundary := closedDiskBoundarySet 1
abbrev disk := euclideanClosedDisk 1
local instance : ContractibleSpace disk := Metric.contractibleSpace_closedBall (by norm_num)

def boundaryHomeo : boundary ≃ₜ Bool :=
  T02A06SphereOne.closedDiskOneBoundaryHomeomorphIntervalBoundary.trans
    boolHomeomorphIntervalBoundary.symm

def boundarySigmaIso : (F R).obj (TopCat.of boundary) ≅ ∐ fun _ : Bool => ModuleCat.of R R :=
  (F R).mapIso (TopCat.isoOfHomeo boundaryHomeo) ≪≫
    directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Bool

def diskPointEquiv := Classical.choice (ContractibleSpace.hequiv_unit disk)
def diskIso : (F R).obj (TopCat.of disk) ≅ ModuleCat.of R R :=
  CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv R diskPointEquiv 0 ≪≫
    directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Unit ≪≫
    coproductUniqueIso (fun _ : Unit => ModuleCat.of R R)

def inclusion := HomologicalComplex.homologyMap
  (CoefficientRelativeSmall.subspaceMap R boundary) 0

theorem sigma_coordinates : (boundarySigmaIso R).inv ≫ inclusion R ≫ (diskIso R).hom =
    Sigma.desc (fun _ : Bool => 𝟙 (ModuleCat.of R R)) := by
  change (directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Bool).inv ≫
    (F R).map (TopCat.isoOfHomeo boundaryHomeo).inv ≫
    (F R).map (subspaceInclusion boundary) ≫
    (F R).map (TopCat.ofHom diskPointEquiv.toFun) ≫
    (directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Unit).hom ≫
    (coproductUniqueIso (fun _ : Unit => ModuleCat.of R R)).hom = _
  have h : (F R).map (TopCat.isoOfHomeo boundaryHomeo).inv ≫
      (F R).map (subspaceInclusion boundary) ≫
      (F R).map (TopCat.ofHom diskPointEquiv.toFun) = (F R).map boolCollapse := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  calc
    _ = (directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Bool).inv ≫
        (F R).map boolCollapse ≫
        (directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Unit).hom ≫
        (coproductUniqueIso (fun _ : Unit => ModuleCat.of R R)).hom := by
      simpa only [Category.assoc] using congrArg (fun g =>
        (directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Bool).inv ≫ g ≫
        (directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Unit).hom ≫
        (coproductUniqueIso (fun _ : Unit => ModuleCat.of R R)).hom) h
    _ = _ := directDiscreteH0Iso_boolCollapse_codiagonal (ModuleCat R) (ModuleCat.of R R)

def boolModuleIso : (∐ fun _ : Bool => ModuleCat.of R R) ≅ ModuleCat.of R (Bool → R) :=
  ModuleCat.coprodIsoDirectSum _ ≪≫
    (DirectSum.linearEquivFunOnFintype R Bool (fun _ => R)).toModuleIso

theorem boolModule_sum : (boolModuleIso R).hom ≫ CoefficientCodiagonalKernel.sumMap R =
    Sigma.desc (fun _ : Bool => 𝟙 (ModuleCat.of R R)) := by
  apply Sigma.hom_ext
  intro b
  rw [Sigma.ι_desc]
  dsimp only [boolModuleIso, Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change ((DirectSum.linearEquivFunOnFintype R Bool (fun _ => R))
    (DirectSum.lof R Bool (fun _ => R) b r)) false +
    ((DirectSum.linearEquivFunOnFintype R Bool (fun _ => R))
    (DirectSum.lof R Bool (fun _ => R) b r)) true = _
  rw [DirectSum.linearEquivFunOnFintype_lof]
  cases b <;> simp

def boundaryIso := boundarySigmaIso R ≪≫ boolModuleIso R

theorem inclusion_coordinates : inclusion R ≫ (diskIso R).hom =
    (boundaryIso R).hom ≫ CoefficientCodiagonalKernel.sumMap R := by
  apply (cancel_epi (boundarySigmaIso R).inv).mp
  apply (sigma_coordinates R).trans
  change _ = (boundarySigmaIso R).inv ≫
    ((boundarySigmaIso R).hom ≫ (boolModuleIso R).hom) ≫ _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (boolModule_sum R).symm

def boundaryKernelIso : kernel (inclusion R) ≅ ModuleCat.of R R :=
  kernel.mapIso (f := inclusion R) (CoefficientCodiagonalKernel.sumMap R) (boundaryIso R) (diskIso R)
    (inclusion_coordinates R) ≪≫ CoefficientCodiagonalKernel.kernelIso R

def circleH1 : CoefficientContractiblePair.H R 1
    (TopCat.of (T02A06HemisphereExcision.ambientSphere 1)) ≅ ModuleCat.of R R :=
  CoefficientSphereShift.sphereH1KernelIso R 1 ≪≫ boundaryKernelIso R

def sphereH2 : CoefficientContractiblePair.H R 2
    (TopCat.of (T02A06HemisphereExcision.ambientSphere 2)) ≅ ModuleCat.of R R :=
  CoefficientSphereShift.sphereShift R 2 1 (by decide) ≪≫ circleH1 R

theorem boundaryKernelIso_hom : (boundaryKernelIso R).hom =
    kernel.map (inclusion R) (CoefficientCodiagonalKernel.sumMap R)
      (boundaryIso R).hom (diskIso R).hom (inclusion_coordinates R) ≫
    (CoefficientCodiagonalKernel.kernelIso R).hom := rfl

theorem kernel_signed_projection : (boundaryKernelIso R).inv ≫ kernel.ι (inclusion R) ≫
    (boundaryIso R).hom = CoefficientCodiagonalKernel.signedMap R := by
  let t := kernel.mapIso (f := inclusion R) (CoefficientCodiagonalKernel.sumMap R)
    (boundaryIso R) (diskIso R) (inclusion_coordinates R)
  have h : t.hom ≫ kernel.ι (CoefficientCodiagonalKernel.sumMap R) =
      kernel.ι (inclusion R) ≫ (boundaryIso R).hom := kernel.lift_ι _ _ _
  change (CoefficientCodiagonalKernel.kernelIso R).inv ≫ t.inv ≫
    kernel.ι (inclusion R) ≫ (boundaryIso R).hom = _
  rw [← h, t.inv_hom_id_assoc]
  exact CoefficientCodiagonalKernel.inverse_projection R

theorem kernel_false (r : R) : (boundaryIso R).hom.hom
    ((kernel.ι (inclusion R)).hom ((boundaryKernelIso R).inv.hom r)) false = r :=
  congrArg (fun f => f.hom r false) (kernel_signed_projection R)

theorem kernel_true (r : R) : (boundaryIso R).hom.hom
    ((kernel.ι (inclusion R)).hom ((boundaryKernelIso R).inv.hom r)) true = -r :=
  congrArg (fun f => f.hom r true) (kernel_signed_projection R)

theorem circleH1_hom : (circleH1 R).hom =
    (CoefficientSphereShift.sphereH1KernelIso R 1).hom ≫ (boundaryKernelIso R).hom := rfl

theorem sphereH2_hom : (sphereH2 R).hom =
    (CoefficientSphereShift.sphereShift R 2 1 (by decide)).hom ≫
    (CoefficientSphereShift.sphereH1KernelIso R 1).hom ≫ (boundaryKernelIso R).hom := rfl

def sphereH1 : CoefficientContractiblePair.H R 1
    (TopCat.of (T02A06HemisphereExcision.ambientSphere 2)) ≅ ModuleCat.of R (Fin 0 → R) :=
  (CoefficientConnectedH0Map.sphereTwo_H1_zero R).iso
    (ModuleCat.isZero_of_subsingleton _)

def sphereH0 := CoefficientH0.sphereH0 R 2

theorem circle_inverse_left : (circleH1 R).inv ≫ (circleH1 R).hom = 𝟙 _ := (circleH1 R).inv_hom_id
theorem circle_inverse_right : (circleH1 R).hom ≫ (circleH1 R).inv = 𝟙 _ := (circleH1 R).hom_inv_id
theorem sphere_two_inverse_left : (sphereH2 R).inv ≫ (sphereH2 R).hom = 𝟙 _ := (sphereH2 R).inv_hom_id
theorem sphere_two_inverse_right : (sphereH2 R).hom ≫ (sphereH2 R).inv = 𝟙 _ := (sphereH2 R).hom_inv_id
theorem sphere_one_inverse_left : (sphereH1 R).inv ≫ (sphereH1 R).hom = 𝟙 _ := (sphereH1 R).inv_hom_id
theorem sphere_one_inverse_right : (sphereH1 R).hom ≫ (sphereH1 R).inv = 𝟙 _ := (sphereH1 R).hom_inv_id

theorem identity_coordinates {X : Type} [TopologicalSpace X] (n : ℕ) {M : ModuleCat R}
    (e : CoefficientContractiblePair.H R n (TopCat.of X) ≅ M) :
    e.inv ≫ (CoefficientRadialPair.F R n).map (𝟙 (TopCat.of X)) ≫ e.hom = 𝟙 M := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp, e.inv_hom_id]

def rationalS2H0 := sphereH0 ℚ
def rationalS2H1 := sphereH1 ℚ
def rationalS2H2 := sphereH2 ℚ
def integralS1H1 := circleH1 ℤ
def integralS2H1 := sphereH1 ℤ
def integralS2H2 := sphereH2 ℤ

theorem rational_identity_zero : rationalS2H0.inv ≫ (CoefficientRadialPair.F ℚ 0).map
    (𝟙 (TopCat.of (T02A06HemisphereExcision.ambientSphere 2))) ≫ rationalS2H0.hom = 𝟙 _ :=
  identity_coordinates ℚ 0 rationalS2H0

theorem rational_identity_one : rationalS2H1.inv ≫ (CoefficientRadialPair.F ℚ 1).map
    (𝟙 (TopCat.of (T02A06HemisphereExcision.ambientSphere 2))) ≫ rationalS2H1.hom = 𝟙 _ :=
  identity_coordinates ℚ 1 rationalS2H1

theorem rational_identity_two : rationalS2H2.inv ≫ (CoefficientRadialPair.F ℚ 2).map
    (𝟙 (TopCat.of (T02A06HemisphereExcision.ambientSphere 2))) ≫ rationalS2H2.hom = 𝟙 _ :=
  identity_coordinates ℚ 2 rationalS2H2

#print axioms boundaryKernelIso_hom
#print axioms sigma_coordinates
#print axioms boolModule_sum
#print axioms inclusion_coordinates
#print axioms kernel_signed_projection
#print axioms kernel_false
#print axioms kernel_true
#print axioms circleH1_hom
#print axioms sphereH2_hom
#print axioms sphereH1
#print axioms circle_inverse_left
#print axioms circle_inverse_right
#print axioms sphere_two_inverse_left
#print axioms sphere_two_inverse_right
#print axioms sphere_one_inverse_left
#print axioms sphere_one_inverse_right
#print axioms rationalS2H0
#print axioms rationalS2H1
#print axioms rationalS2H2
#print axioms integralS1H1
#print axioms integralS2H1
#print axioms integralS2H2
#print axioms rational_identity_zero
#print axioms rational_identity_one
#print axioms rational_identity_two
end ConstructionTargets.CoefficientSphereEndpoints
