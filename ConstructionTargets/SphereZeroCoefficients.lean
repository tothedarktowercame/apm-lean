import ConstructionTargets.SphereHomology
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ConstructionTargets.SphereZeroCoefficients
open SphereHomology SingularHomologyConcrete
variable (R : Type) [CommRing R]
abbrev H (k : ℕ) := (((AlgebraicTopology.singularHomologyFunctor (ModuleCat R) k).obj
    (ModuleCat.of R R)).obj (TopCat.of (Sphere 0)))
def positivePoint : Sphere 0 := ⟨WithLp.toLp 2 (fun _ => 1), by
  unfold Sphere
  rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one]; simp⟩
def negativePoint : Sphere 0 := ⟨WithLp.toLp 2 (fun _ => -1), by
  unfold Sphere
  rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one]; simp⟩
def coordinates : Sphere 0 ≃ Bool where
  toFun := sphereZeroSign
  invFun := fun b => if b then positivePoint else negativePoint
  left_inv x := by
    apply sphereZeroSign_injective
    rcases sphereZero_coord x with hx | hx <;>
      norm_num [sphereZeroSign, hx, positivePoint, negativePoint]
  right_inv b := by cases b <;> norm_num [sphereZeroSign, positivePoint, negativePoint]

noncomputable def h0Coordinates : H R 0 ≅ ModuleCat.of R (Bool → R) := by
  letI : Fintype (Sphere 0) := Fintype.ofFinite _
  exact directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) (Sphere 0) ≪≫
    ModuleCat.coprodIsoDirectSum _ ≪≫
    (DirectSum.linearEquivFunOnFintype R (Sphere 0) (fun _ => R)).toModuleIso ≪≫
    (LinearEquiv.funCongrLeft R R coordinates.symm).toModuleIso

theorem positive_vanishing (k : ℕ) (hk : 0 < k) : IsZero (H R k) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat R) k (ModuleCat.of R R) (TopCat.of (Sphere 0)) (Nat.ne_of_gt hk)

def rationalH0 := h0Coordinates ℚ
def integralH0 := h0Coordinates ℤ
#print axioms coordinates
#print axioms h0Coordinates
#print axioms positive_vanishing
#print axioms rationalH0
#print axioms integralH0
end ConstructionTargets.SphereZeroCoefficients
