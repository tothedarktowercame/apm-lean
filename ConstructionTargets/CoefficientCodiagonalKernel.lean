import ConstructionTargets.CoefficientSphereShift
import Mathlib.Algebra.Category.ModuleCat.Kernels
noncomputable section
namespace ConstructionTargets.CoefficientCodiagonalKernel
open CategoryTheory CategoryTheory.Limits
variable (R : Type) [CommRing R]

def sumMap : ModuleCat.of R (Bool → R) ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom ((LinearMap.proj false : (Bool → R) →ₗ[R] R) + LinearMap.proj true)

def signedMap : ModuleCat.of R R ⟶ ModuleCat.of R (Bool → R) :=
  ModuleCat.ofHom {
    toFun := fun r b => if b then -r else r
    map_add' := by intro x y; funext b; cases b <;> simp [add_comm]
    map_smul' := by intro x y; funext b; cases b <;> simp }

theorem signed_sum : signedMap R ≫ sumMap R = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  simp [signedMap, sumMap]

def kerEquiv : LinearMap.ker (sumMap R).hom ≃ₗ[R] R where
  toFun x := x.1 false
  invFun r := ⟨fun b => if b then -r else r, by simp [LinearMap.mem_ker, sumMap]⟩
  left_inv x := by
    apply Subtype.ext
    funext b
    have h : x.1 false + x.1 true = 0 := x.2
    cases b
    · rfl
    · exact (eq_neg_of_add_eq_zero_right h).symm
  right_inv r := rfl
  map_add' x y := rfl
  map_smul' r x := rfl

def kernelIso : kernel (sumMap R) ≅ ModuleCat.of R R :=
  ModuleCat.kernelIsoKer (sumMap R) ≪≫ (kerEquiv R).toModuleIso

theorem inverse_projection : (kernelIso R).inv ≫ kernel.ι (sumMap R) = signedMap R := by
  change ((kerEquiv R).toModuleIso.inv ≫ (ModuleCat.kernelIsoKer (sumMap R)).inv) ≫ _ = _
  rw [Category.assoc, ModuleCat.kernelIsoKer_inv_kernel_ι]
  rfl

theorem inverse_false (r : R) : (kernel.ι (sumMap R)).hom ((kernelIso R).inv.hom r) false = r := by
  have h := congrArg (fun f => f.hom r false) (inverse_projection R)
  exact h

theorem inverse_true (r : R) : (kernel.ι (sumMap R)).hom ((kernelIso R).inv.hom r) true = -r := by
  have h := congrArg (fun f => f.hom r true) (inverse_projection R)
  exact h

theorem forward_coordinate : (kernelIso R).hom = kernel.ι (sumMap R) ≫
    ModuleCat.ofHom (LinearMap.proj false) := by
  change (ModuleCat.kernelIsoKer (sumMap R)).hom ≫ (kerEquiv R).toModuleIso.hom = _
  rw [← ModuleCat.kernelIsoKer_hom_ker_subtype (sumMap R), Category.assoc]
  rfl

theorem inverse_left : (kernelIso R).inv ≫ (kernelIso R).hom = 𝟙 _ :=
  (kernelIso R).inv_hom_id

theorem inverse_right : (kernelIso R).hom ≫ (kernelIso R).inv = 𝟙 _ :=
  (kernelIso R).hom_inv_id

theorem integral_generator : (kernel.ι (sumMap ℤ)).hom ((kernelIso ℤ).inv.hom 1) false = 1 := inverse_false ℤ 1
theorem rational_half_generator : (kernel.ι (sumMap ℚ)).hom ((kernelIso ℚ).inv.hom (1/2)) true = -(1/2) := inverse_true ℚ (1/2)
#print axioms integral_generator
#print axioms rational_half_generator
#print axioms signed_sum
#print axioms kerEquiv
#print axioms inverse_projection
#print axioms forward_coordinate
#print axioms inverse_left
#print axioms inverse_right
#print axioms inverse_false
#print axioms inverse_true
end ConstructionTargets.CoefficientCodiagonalKernel
