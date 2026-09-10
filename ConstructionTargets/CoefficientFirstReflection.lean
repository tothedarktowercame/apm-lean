import ConstructionTargets.CoefficientCoordinateReflections
noncomputable section
namespace ConstructionTargets.CoefficientFirstReflection
open CategoryTheory CategoryTheory.Limits
open T02A06 T02A06HemisphereExcision
open CoefficientCoordinateReflections CoefficientOrthogonalSphere
variable (R : Type) [CommRing R]

theorem extended_reflection {d : ℕ} (i : Fin d) :
    sphereAction (reflection i) = reflectionMap i.castSucc := by
  ext x j
  change euclideanSnoc (reflection i (euclideanInit x.1)) (sphereHeight d x) j =
    reflection i.castSucc x.1 j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have h : Fin.last d ≠ i.castSucc := by intro h; have := congrArg Fin.val h; simp at this; omega
    simp [euclideanSnoc_last, reflection_apply, sphereHeight, h]
  · simp [euclideanSnoc, reflection_apply, euclideanInit, Fin.init]

theorem boundary_reflection {d : ℕ} (i : Fin d) :
    CoefficientOrthogonalRadial.boundaryAction (reflection i) = reflectionMap i := rfl

theorem homology_actual {d : ℕ} (Q : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (q : ℕ) :
    sphereHomologyMap R Q q = (H R q).map (TopCat.ofHom (sphereAction Q)) := rfl

private theorem negative_of_intertwining {A B : ModuleCat R} (e : A ≅ B)
    (a : A ⟶ A) (b : B ⟶ B) (h : a ≫ e.hom = e.hom ≫ b) (hb : b = -𝟙 _) :
    a = -𝟙 _ := by
  apply (cancel_mono e.hom).mp
  simpa only [hb, Preadditive.comp_neg, Preadditive.neg_comp, Category.comp_id, Category.id_comp] using h

theorem reflection_one : reflection (0 : Fin 1) =
    LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin 1)) := by
  ext x j
  fin_cases j
  simp [reflection_apply]

theorem circle_negative : (H R 1).map (TopCat.ofHom (reflectionMap (0 : Fin 2))) = -𝟙 _ := by
  have hn := sphereToDisk_naturality R (reflection (0 : Fin 1)) 1 (by decide)
  have hd : HomologicalComplex.homologyMap
      (CoefficientOrthogonalRadial.closedPair R (reflection (0 : Fin 1))) 1 = -𝟙 _ := by
    rw [reflection_one]
    exact CoefficientDiskReflection.relative_eq_neg_id R
  have hh := negative_of_intertwining R _ _ _ hn hd
  rw [homology_actual, extended_reflection] at hh
  exact hh

theorem all_reflections_negative (n : ℕ) (hn : n ≠ 0) (i : Fin (n+1)) :
    (H R n).map (TopCat.ofHom (reflectionMap i)) = -𝟙 _ := by
  induction n with
  | zero => exact (hn rfl).elim
  | succ n ih =>
    cases n with
    | zero => exact transport_any_coordinate R 1 0 i (circle_negative R)
    | succ m =>
      have hs := sphereShift_naturality R (reflection (0 : Fin (m+2))) (m+1) (by omega)
      have hb : boundaryHomologyMap R (reflection (0 : Fin (m+2))) (m+1) = -𝟙 _ :=
        ih (by omega) 0
      have hh := negative_of_intertwining R _ _ _ hs hb
      rw [homology_actual, extended_reflection] at hh
      exact transport_any_coordinate R (m+2) _ i hh

def topIso : (m : ℕ) →
    (H R (m+1)).obj (TopCat.of (euclideanUnitSphere (m+2))) ≅ ModuleCat.of R R
  | 0 => CoefficientSphereEndpoints.circleH1 R
  | m+1 => CoefficientSphereShift.sphereShift R (m+2) (m+1) (by omega) ≪≫ topIso m


theorem topIso_step (m : ℕ) : (topIso R (m+1)).hom =
    (CoefficientSphereShift.sphereShift R (m+2) (m+1) (by omega)).hom ≫ (topIso R m).hom := by
  rw [topIso]
  rfl

theorem normalized_reflection (m : ℕ) (i : Fin (m+2)) :
    (H R (m+1)).map (TopCat.ofHom (reflectionMap i)) ≫ (topIso R m).hom = -(topIso R m).hom := by
  rw [all_reflections_negative R (m+1) (by omega)]
  simp only [Preadditive.neg_comp, Category.id_comp]

theorem reflection_conjugation (m : ℕ) (i : Fin (m+2)) :
    (topIso R m).inv ≫ (H R (m+1)).map (TopCat.ofHom (reflectionMap i)) ≫ (topIso R m).hom = -𝟙 _ := by
  rw [normalized_reflection]
  simp only [Preadditive.comp_neg, Iso.inv_hom_id]

theorem inverse_left (m : ℕ) : (topIso R m).inv ≫ (topIso R m).hom = 𝟙 _ :=
  (topIso R m).inv_hom_id

theorem inverse_right (m : ℕ) : (topIso R m).hom ≫ (topIso R m).inv = 𝟙 _ :=
  (topIso R m).hom_inv_id

def integral_circle := all_reflections_negative ℤ 1 (by decide)
def rational_sphereTwo := all_reflections_negative ℚ 2 (by decide)
def rational_circle := reflection_conjugation ℚ 0
def integral_sphereTwo := reflection_conjugation ℤ 1
end ConstructionTargets.CoefficientFirstReflection

#print axioms ConstructionTargets.CoefficientFirstReflection.extended_reflection
#print axioms ConstructionTargets.CoefficientFirstReflection.circle_negative
#print axioms ConstructionTargets.CoefficientFirstReflection.all_reflections_negative
#print axioms ConstructionTargets.CoefficientFirstReflection.topIso
#print axioms ConstructionTargets.CoefficientFirstReflection.topIso_step
#print axioms ConstructionTargets.CoefficientFirstReflection.normalized_reflection
#print axioms ConstructionTargets.CoefficientFirstReflection.reflection_conjugation
#print axioms ConstructionTargets.CoefficientFirstReflection.inverse_left
#print axioms ConstructionTargets.CoefficientFirstReflection.inverse_right
#print axioms ConstructionTargets.CoefficientFirstReflection.integral_circle
#print axioms ConstructionTargets.CoefficientFirstReflection.rational_sphereTwo
#print axioms ConstructionTargets.CoefficientFirstReflection.rational_circle
#print axioms ConstructionTargets.CoefficientFirstReflection.integral_sphereTwo
