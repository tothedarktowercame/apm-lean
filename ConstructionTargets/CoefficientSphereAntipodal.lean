import ConstructionTargets.CoefficientFirstReflection
noncomputable section
namespace ConstructionTargets.CoefficientSphereAntipodal
open CategoryTheory CategoryTheory.Limits T02A06
open CoefficientCoordinateReflections CoefficientFirstReflection
variable {d : ℕ}

def reflectionProduct : List (Fin d) → C(euclideanUnitSphere d, euclideanUnitSphere d)
  | [] => ContinuousMap.id _
  | i :: l => (reflectionMap i).comp (reflectionProduct l)

theorem product_coordinate (l : List (Fin d)) (hl : l.Nodup) (x : euclideanUnitSphere d) (j : Fin d) :
    (reflectionProduct l x).1 j = if j ∈ l then -x.1 j else x.1 j := by
  induction l with
  | nil => simp [reflectionProduct]
  | cons i l ih =>
    have hi := List.nodup_cons.mp hl
    change reflection i (reflectionProduct l x).1 j = _
    rw [reflection_apply, ih hi.2]
    by_cases h : j = i
    · subst j; simp [hi.1]
    · simp [h]

def antipodal : C(euclideanUnitSphere d, euclideanUnitSphere d) where
  toFun x := ⟨-x.1, by simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using x.2⟩
  continuous_toFun := by fun_prop

theorem product_antipodal : reflectionProduct (List.finRange d) = antipodal := by
  ext x j
  change (reflectionProduct (List.finRange d) x).1 j = -x.1 j
  simpa using product_coordinate (List.finRange d) (List.nodup_finRange d) x j

variable (R : Type) [CommRing R]

theorem product_homology (n : ℕ) (hn : n ≠ 0) (l : List (Fin (n+1))) :
    (H R n).map (TopCat.ofHom (reflectionProduct l)) =
      ((-1 : R)^l.length) • 𝟙 _ := by
  induction l with
  | nil => simp [reflectionProduct]
  | cons i l ih =>
    have hc : TopCat.ofHom (reflectionProduct (i :: l)) =
        TopCat.ofHom (reflectionProduct l) ≫ TopCat.ofHom (reflectionMap i) := rfl
    rw [hc, Functor.map_comp, ih, all_reflections_negative R n hn i]
    simp [pow_succ, Preadditive.comp_neg]

theorem antipodal_action (n : ℕ) (hn : n ≠ 0) :
    (H R n).map (TopCat.ofHom (antipodal (d := n+1))) = ((-1 : R)^(n+1)) • 𝟙 _ := by
  rw [← product_antipodal]
  simpa using product_homology R n hn (List.finRange (n+1))

def normalization (m : ℕ) := topIso R m

theorem normalization_forward (m : ℕ) :
    (H R (m+1)).map (TopCat.ofHom (antipodal (d := m+2))) ≫ (normalization R m).hom =
      ((-1 : R)^(m+2)) • (normalization R m).hom := by
  rw [antipodal_action R (m+1) (by omega)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (normalization R m).hom.hom.map_smul _ x

theorem normalization_conjugation (m : ℕ) :
    (normalization R m).inv ≫ (H R (m+1)).map (TopCat.ofHom (antipodal (d := m+2))) ≫
      (normalization R m).hom = ((-1 : R)^(m+2)) • 𝟙 _ := by
  rw [normalization_forward]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact congrArg (fun f => ((-1 : R)^(m+2)) * f.hom r) (normalization R m).inv_hom_id

theorem scalar_equation (m : ℕ)
    (a : (H R (m+1)).obj (TopCat.of (euclideanUnitSphere (m+2)))) :
    (normalization R m).hom.hom
      (((H R (m+1)).map (TopCat.ofHom (antipodal (d := m+2)))).hom a) =
      (-1 : R)^(m+2) * (normalization R m).hom.hom a := by
  exact congrArg (fun f => f.hom a) (normalization_forward R m)

theorem inverse_left (m : ℕ) : (normalization R m).inv ≫ (normalization R m).hom = 𝟙 _ :=
  (normalization R m).inv_hom_id

theorem inverse_right (m : ℕ) : (normalization R m).hom ≫ (normalization R m).inv = 𝟙 _ :=
  (normalization R m).hom_inv_id

theorem inverse_action (m : ℕ) :
    (normalization R m).inv ≫ (H R (m+1)).map (TopCat.ofHom (antipodal (d := m+2))) =
      ((-1 : R)^(m+2)) • (normalization R m).inv := by
  rw [antipodal_action R (m+1) (by omega)]
  rfl

def integral_circle := normalization_conjugation ℤ 0
def integral_sphereTwo := normalization_conjugation ℤ 1
def rational_circle := normalization_conjugation ℚ 0
def rational_sphereTwo := normalization_conjugation ℚ 1

theorem circle_scalar (a : (H R 1).obj (TopCat.of (euclideanUnitSphere 2))) :
    (normalization R 0).hom.hom (((H R 1).map (TopCat.ofHom antipodal)).hom a) =
      (normalization R 0).hom.hom a := by
  simpa using scalar_equation R 0 a

theorem sphereTwo_scalar (a : (H R 2).obj (TopCat.of (euclideanUnitSphere 3))) :
    (normalization R 1).hom.hom (((H R 2).map (TopCat.ofHom antipodal)).hom a) =
      -(normalization R 1).hom.hom a := by
  simpa only [show (1+2 : ℕ) = 3 from rfl, pow_succ, pow_zero, mul_one, one_mul, mul_neg_one, neg_one_mul, neg_neg] using scalar_equation R 1 a

end ConstructionTargets.CoefficientSphereAntipodal



#print axioms ConstructionTargets.CoefficientSphereAntipodal.product_coordinate
#print axioms ConstructionTargets.CoefficientSphereAntipodal.antipodal
#print axioms ConstructionTargets.CoefficientSphereAntipodal.product_antipodal
#print axioms ConstructionTargets.CoefficientSphereAntipodal.product_homology
#print axioms ConstructionTargets.CoefficientSphereAntipodal.antipodal_action
#print axioms ConstructionTargets.CoefficientSphereAntipodal.normalization
#print axioms ConstructionTargets.CoefficientSphereAntipodal.normalization_forward
#print axioms ConstructionTargets.CoefficientSphereAntipodal.normalization_conjugation
#print axioms ConstructionTargets.CoefficientSphereAntipodal.scalar_equation
#print axioms ConstructionTargets.CoefficientSphereAntipodal.inverse_left
#print axioms ConstructionTargets.CoefficientSphereAntipodal.inverse_right
#print axioms ConstructionTargets.CoefficientSphereAntipodal.inverse_action
#print axioms ConstructionTargets.CoefficientSphereAntipodal.integral_circle
#print axioms ConstructionTargets.CoefficientSphereAntipodal.integral_sphereTwo
#print axioms ConstructionTargets.CoefficientSphereAntipodal.rational_circle
#print axioms ConstructionTargets.CoefficientSphereAntipodal.rational_sphereTwo
#print axioms ConstructionTargets.CoefficientSphereAntipodal.circle_scalar
#print axioms ConstructionTargets.CoefficientSphereAntipodal.sphereTwo_scalar
