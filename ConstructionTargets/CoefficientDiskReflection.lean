import ConstructionTargets.CoefficientBoundaryReflection
noncomputable section
namespace ConstructionTargets.CoefficientDiskReflection
open CategoryTheory CategoryTheory.Limits
open CoefficientSphereEndpoints CoefficientBoundaryReflection
variable (R : Type) [CommRing R]
local instance : ContractibleSpace disk := Metric.contractibleSpace_closedBall (by norm_num)

def kernelMap : kernel (inclusion R) ⟶ kernel (inclusion R) :=
  kernel.map (inclusion R) (inclusion R) (boundaryMap R)
    (HomologicalComplex.homologyMap (absolute R) 0) (inclusion_square R)

theorem kernel_projection : kernelMap R ≫ kernel.ι (inclusion R) =
    kernel.ι (inclusion R) ≫ boundaryMap R := kernel.lift_ι _ _ _

theorem signed_swap : CoefficientCodiagonalKernel.signedMap R ≫ swap R =
    -CoefficientCodiagonalKernel.signedMap R := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  funext b
  cases b <;> simp [CoefficientCodiagonalKernel.signedMap, swap]

theorem kernel_inverse_action : (boundaryKernelIso R).inv ≫ kernelMap R =
    -(boundaryKernelIso R).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply (ModuleCat.mono_iff_injective (kernel.ι (inclusion R) ≫ (boundaryIso R).hom)).mp inferInstance
  have hp := congrArg (fun f => f.hom ((boundaryKernelIso R).inv.hom r)) (kernel_projection R)
  have hc := congrArg (fun f => f.hom ((kernel.ι (inclusion R)).hom ((boundaryKernelIso R).inv.hom r)))
    (boundary_coordinates R)
  have hs := congrArg (fun f => f.hom r) (kernel_signed_projection R)
  have hn := congrArg (fun f => f.hom r) (signed_swap R)
  change (boundaryIso R).hom.hom ((kernel.ι (inclusion R)).hom
    ((kernelMap R).hom ((boundaryKernelIso R).inv.hom r))) =
    (boundaryIso R).hom.hom ((kernel.ι (inclusion R)).hom (-((boundaryKernelIso R).inv.hom r)))
  change (kernel.ι (inclusion R)).hom ((kernelMap R).hom _) = (boundaryMap R).hom _ at hp
  change (boundaryIso R).hom.hom ((boundaryMap R).hom _) = (swap R).hom _ at hc
  change (boundaryIso R).hom.hom ((kernel.ι (inclusion R)).hom _) = _ at hs
  exact (congrArg (boundaryIso R).hom.hom hp).trans (hc.trans
    ((congrArg (swap R).hom hs).trans (hn.trans
      ((congrArg Neg.neg hs.symm).trans
        ((congrArg (boundaryIso R).hom.hom ((kernel.ι (inclusion R)).hom.map_neg _)).trans
          ((boundaryIso R).hom.hom.map_neg _)).symm))))

def relativeMap := HomologicalComplex.homologyMap (relative R) 1

def connectingIso := CoefficientContractiblePair.contractibleH1KernelIso R boundary

def normalization := connectingIso R ≪≫ boundaryKernelIso R

theorem connecting_kernel_naturality : relativeMap R ≫ (connectingIso R).hom =
    (connectingIso R).hom ≫ kernelMap R := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (ModuleCat.mono_iff_injective (kernel.ι (inclusion R))).mp inferInstance
  have hp := congrArg (fun f => f.hom ((connectingIso R).hom.hom x)) (kernel_projection R)
  have he := CoefficientContractiblePair.contractibleH1Kernel_projection R boundary
  have he1 := congrArg (fun f => f.hom x) he
  have he2 := congrArg (fun f => f.hom ((relativeMap R).hom x)) he
  have hn := congrArg (fun f => f.hom x)
    (CoefficientPairNaturality.connecting_naturality R boundary boundary reflection reflection_mapsTo 0)
  change (kernel.ι (inclusion R)).hom ((connectingIso R).hom.hom ((relativeMap R).hom x)) =
    (kernel.ι (inclusion R)).hom ((kernelMap R).hom ((connectingIso R).hom.hom x))
  exact he2.trans (hn.symm.trans ((congrArg (boundaryMap R).hom he1.symm).trans hp.symm))

theorem kernel_conjugation : (boundaryKernelIso R).inv ≫ kernelMap R ≫ (boundaryKernelIso R).hom = -𝟙 _ := by
  rw [← Category.assoc, kernel_inverse_action, Preadditive.neg_comp, Iso.inv_hom_id]

theorem relative_conjugation : (normalization R).inv ≫ relativeMap R ≫ (normalization R).hom = -𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  have hn := congrArg (fun f => f.hom ((normalization R).inv.hom r)) (connecting_kernel_naturality R)
  have hi := congrArg (fun f => f.hom ((boundaryKernelIso R).inv.hom r)) (connectingIso R).inv_hom_id
  have hk := congrArg (fun f => f.hom r) (kernel_conjugation R)
  change (boundaryKernelIso R).hom.hom ((connectingIso R).hom.hom
    ((relativeMap R).hom ((normalization R).inv.hom r))) = -r
  exact (congrArg (boundaryKernelIso R).hom.hom hn).trans
    ((congrArg (fun x => (boundaryKernelIso R).hom.hom ((kernelMap R).hom x)) hi).trans hk)

theorem normalization_hom : (normalization R).hom =
    (CoefficientContractiblePair.contractibleH1KernelIso R boundary).hom ≫ (boundaryKernelIso R).hom := rfl

theorem normalization_inverse_left : (normalization R).inv ≫ (normalization R).hom = 𝟙 _ :=
  (normalization R).inv_hom_id

theorem normalization_inverse_right : (normalization R).hom ≫ (normalization R).inv = 𝟙 _ :=
  (normalization R).hom_inv_id

theorem relative_forward : relativeMap R ≫ (normalization R).hom = -(normalization R).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hi := congrArg (fun f => f.hom x) (normalization R).hom_inv_id
  have hn := congrArg (fun f => f.hom ((normalization R).hom.hom x)) (relative_conjugation R)
  exact (congrArg (fun y => (normalization R).hom.hom ((relativeMap R).hom y)) hi).symm.trans hn

theorem relative_eq_neg_id : relativeMap R = -𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (ModuleCat.mono_iff_injective (normalization R).hom).mp inferInstance
  exact (congrArg (fun f => f.hom x) (relative_forward R)).trans
    ((normalization R).hom.hom.map_neg x).symm

def integral_sign := relative_conjugation ℤ
def rational_sign := relative_conjugation ℚ

/- R is any Type 0 commutative ring, with no nontriviality or characteristic
restriction. Ordinary boundary H0 remains the two-coordinate module. -/

#print axioms kernelMap
#print axioms kernel_projection
#print axioms signed_swap
#print axioms kernel_inverse_action
#print axioms connecting_kernel_naturality
#print axioms kernel_conjugation
#print axioms normalization_hom
#print axioms normalization_inverse_left
#print axioms normalization_inverse_right
#print axioms relative_conjugation
#print axioms relative_forward
#print axioms relative_eq_neg_id
#print axioms integral_sign
#print axioms rational_sign

end ConstructionTargets.CoefficientDiskReflection
