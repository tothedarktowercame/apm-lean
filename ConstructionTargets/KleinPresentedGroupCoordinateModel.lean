import Mathlib
import ConstructionTargets.StatementSurfaceModels

open ConstructionTargets.StatementSurfaceModels
noncomputable section

namespace KleinPresentedGroupCoordinateModel

abbrev ZMul := Multiplicative ℤ

def inversion : MulAut ZMul := MulEquiv.inv ZMul

def action : ZMul →* MulAut ZMul := zpowersHom (MulAut ZMul) inversion

abbrev Coordinates := ZMul ⋊[action] ZMul

def A : Coordinates := SemidirectProduct.inl (Multiplicative.ofAdd 1)
def B : Coordinates := SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[simp] theorem action_one (z : ZMul) : action (Multiplicative.ofAdd 1) z = z⁻¹ := by
  rfl

@[simp] theorem relation : B⁻¹ * A * B * A = 1 := by
  change (SemidirectProduct.inr (φ := action) (Multiplicative.ofAdd 1))⁻¹ *
      SemidirectProduct.inl (φ := action) (Multiplicative.ofAdd 1) *
      SemidirectProduct.inr (φ := action) (Multiplicative.ofAdd 1) *
      SemidirectProduct.inl (φ := action) (Multiplicative.ofAdd 1) = 1
  rw [← map_inv, ← SemidirectProduct.inl_aut_inv]
  ext <;> norm_num [action, inversion]

def relations : Set (FreeGroup Bool) :=
  {((FreeGroup.of true)⁻¹ * FreeGroup.of false * FreeGroup.of true * FreeGroup.of false)}

abbrev PresentedKleinGroup := PresentedGroup relations

def generatorA : PresentedKleinGroup := PresentedGroup.of false
def generatorB : PresentedKleinGroup := PresentedGroup.of true

def toCoordinates : PresentedKleinGroup →* Coordinates :=
  PresentedGroup.toGroup (f := fun x => if x then B else A) (by
    intro r hr
    change r ∈ ({(FreeGroup.of true)⁻¹ * FreeGroup.of false *
      FreeGroup.of true * FreeGroup.of false} : Set (FreeGroup Bool)) at hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    simp [relation])

@[simp] theorem toCoordinates_a : toCoordinates generatorA = A := by
  simp [toCoordinates, generatorA]

@[simp] theorem toCoordinates_b : toCoordinates generatorB = B := by
  simp [toCoordinates, generatorB]

#print axioms relation
#print axioms toCoordinates

end KleinPresentedGroupCoordinateModel
