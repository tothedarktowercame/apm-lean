import ConstructionTargets.CoefficientOrthogonalSphere
noncomputable section
namespace ConstructionTargets.CoefficientCoordinateReflections
open CategoryTheory CategoryTheory.Limits
open T02A06
variable {d : ℕ}

def reflection (i : Fin d) : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

theorem reflection_apply (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    reflection i x j = if j = i then -x j else x j := by
  by_cases h : j = i <;> simp [reflection, LinearIsometryEquiv.piLpCongrRight_apply, h]

def permutation (e : Equiv.Perm (Fin d)) : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

theorem permutation_apply (e : Equiv.Perm (Fin d)) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    permutation e x j = x (e.symm j) := rfl

def sphereHomeo (Q : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    euclideanUnitSphere d ≃ₜ euclideanUnitSphere d :=
  Q.toHomeomorph.subtype (fun x => by
    change ‖x - 0‖ = 1 ↔ ‖Q x - 0‖ = 1
    simp only [sub_zero, Q.norm_map])

def reflectionMap (i : Fin d) : C(euclideanUnitSphere d, euclideanUnitSphere d) :=
  ⟨sphereHomeo (reflection i), (sphereHomeo (reflection i)).continuous⟩

def permutationMap (e : Equiv.Perm (Fin d)) : C(euclideanUnitSphere d, euclideanUnitSphere d) :=
  ⟨sphereHomeo (permutation e), (sphereHomeo (permutation e)).continuous⟩

theorem conjugation (e : Equiv.Perm (Fin d)) (i : Fin d) :
    (permutationMap e).comp ((reflectionMap i).comp (permutationMap e.symm)) = reflectionMap (e i) := by
  ext x j
  change permutation e (reflection i (permutation e.symm x.1)) j = reflection (e i) x.1 j
  simp only [permutation_apply, reflection_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  change (if e.symm j = i then -x.1 j else x.1 j) = if j = e i then -x.1 j else x.1 j
  simp only [Equiv.symm_apply_eq]

theorem permutation_inverse (e : Equiv.Perm (Fin d)) :
    (permutationMap e).comp (permutationMap e.symm) = ContinuousMap.id _ := by
  ext x j
  change permutation e (permutation e.symm x.1) j = x.1 j
  simp only [permutation_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

variable (R : Type) [CommRing R]
abbrev H (q : ℕ) := (AlgebraicTopology.singularHomologyFunctor (ModuleCat R) q).obj (ModuleCat.of R R)

theorem homology_conjugation (q : ℕ) (e : Equiv.Perm (Fin d)) (i : Fin d) :
    (H R q).map (TopCat.ofHom (permutationMap e.symm)) ≫
    (H R q).map (TopCat.ofHom (reflectionMap i)) ≫
    (H R q).map (TopCat.ofHom (permutationMap e)) =
    (H R q).map (TopCat.ofHom (reflectionMap (e i))) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun f => (H R q).map (TopCat.ofHom f)) (conjugation e i)

theorem homology_permutation_inverse (q : ℕ) (e : Equiv.Perm (Fin d)) :
    (H R q).map (TopCat.ofHom (permutationMap e.symm)) ≫
    (H R q).map (TopCat.ofHom (permutationMap e)) = 𝟙 _ := by
  rw [← Functor.map_comp]
  have h := congrArg (fun f => (H R q).map (TopCat.ofHom f)) (permutation_inverse e)
  exact h.trans ((H R q).map_id _)

theorem transport_negative (q : ℕ) (e : Equiv.Perm (Fin d)) (i : Fin d)
    (h : (H R q).map (TopCat.ofHom (reflectionMap i)) = -𝟙 _) :
    (H R q).map (TopCat.ofHom (reflectionMap (e i))) = -𝟙 _ := by
  rw [← homology_conjugation R q e i, h]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp]
  rw [homology_permutation_inverse]

theorem transport_any_coordinate (q : ℕ) (i j : Fin d)
    (h : (H R q).map (TopCat.ofHom (reflectionMap i)) = -𝟙 _) :
    (H R q).map (TopCat.ofHom (reflectionMap j)) = -𝟙 _ := by
  simpa only [Equiv.swap_apply_left] using transport_negative R q (Equiv.swap i j) i h

def integral_conjugation (e : Equiv.Perm (Fin 2)) (i : Fin 2) :=
  homology_conjugation ℤ 1 e i

def rational_conjugation (e : Equiv.Perm (Fin 3)) (i : Fin 3) :=
  homology_conjugation ℚ 2 e i

end ConstructionTargets.CoefficientCoordinateReflections


#print axioms ConstructionTargets.CoefficientCoordinateReflections.reflection
#print axioms ConstructionTargets.CoefficientCoordinateReflections.sphereHomeo
#print axioms ConstructionTargets.CoefficientCoordinateReflections.conjugation
#print axioms ConstructionTargets.CoefficientCoordinateReflections.permutation_inverse
#print axioms ConstructionTargets.CoefficientCoordinateReflections.homology_conjugation
#print axioms ConstructionTargets.CoefficientCoordinateReflections.homology_permutation_inverse
#print axioms ConstructionTargets.CoefficientCoordinateReflections.transport_negative
#print axioms ConstructionTargets.CoefficientCoordinateReflections.transport_any_coordinate
#print axioms ConstructionTargets.CoefficientCoordinateReflections.integral_conjugation
#print axioms ConstructionTargets.CoefficientCoordinateReflections.rational_conjugation
