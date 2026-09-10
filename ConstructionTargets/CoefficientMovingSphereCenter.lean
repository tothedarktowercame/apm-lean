import ConstructionTargets.CoefficientRadialPair
import ConstructionTargets.PuncturedNormedSpaceRadialEquivalence
noncomputable section
namespace ConstructionTargets.CoefficientMovingSphereCenter
open CategoryTheory
open PuncturedNormedSpaceRadialEquivalence
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem avoid_zero (p : E) (hp : ‖p‖ < 1) (t : unitInterval) (z : UnitSphere E) :
    z.val - (t : ℝ) • p ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hz : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.property
  have hlt : ‖(t : ℝ) • p‖ < 1 := by
    rw [norm_smul, Real.norm_of_nonneg t.property.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg p) t.property.2) hp
  rw [← h, hz] at hlt
  exact (lt_irrefl 1 hlt)
def shiftedInclusion (p : E) (hp : ‖p‖ < 1) : C(UnitSphere E, PuncturedSpace E) where
  toFun z := ⟨z.val - p, by simpa using avoid_zero E p hp 1 z⟩
  continuous_toFun := by fun_prop

def shiftHomotopy (p : E) (hp : ‖p‖ < 1) :
    ContinuousMap.Homotopy (unitSphereInclusion E) (shiftedInclusion E p hp) where
  toFun tz := ⟨tz.2.val - (tz.1 : ℝ) • p, avoid_zero E p hp tz.1 tz.2⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by apply Subtype.ext; simp [unitSphereInclusion]
  map_one_left z := by apply Subtype.ext; simp [shiftedInclusion]

def recenteredSphere (p : E) (hp : ‖p‖ < 1) := (radialNormalize E).comp (shiftedInclusion E p hp)
theorem recentered_value (p : E) (hp : ‖p‖ < 1) (z : UnitSphere E) :
    (recenteredSphere E p hp z).val = NormedSpace.normalize (z.val - p) := rfl

def centerFamily : C((Metric.ball (0 : E) 1) × UnitSphere E, PuncturedSpace E) where
  toFun pz := ⟨pz.2.val - pz.1.val, by
    have hp : ‖pz.1.val‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using pz.1.property
    simpa using avoid_zero E pz.1.val hp 1 pz.2⟩
  continuous_toFun := by fun_prop

theorem centerFamily_value (p : Metric.ball (0 : E) 1) (z : UnitSphere E) :
    (centerFamily E (p,z)).val = z.val - p.val := rfl

def betweenCenters (p q : E) (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    ContinuousMap.Homotopy (shiftedInclusion E p hp) (shiftedInclusion E q hq) :=
  (shiftHomotopy E p hp).symm.trans (shiftHomotopy E q hq)

variable (R : Type) [CommRing R]
theorem homology_shift (p : E) (hp : ‖p‖ < 1) (n : ℕ) :
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (unitSphereInclusion E)) =
      (CoefficientRadialPair.F R n).map (TopCat.ofHom (shiftedInclusion E p hp)) :=
  CoefficientContractiblePair.singularHomology_map_eq_of_topCatHomotopy R
    (SingularHomologyConcrete.continuousMapHomotopyCylinder (shiftHomotopy E p hp))
    (SingularHomologyConcrete.continuousMapHomotopyCylinder_zero (shiftHomotopy E p hp))
    (SingularHomologyConcrete.continuousMapHomotopyCylinder_one (shiftHomotopy E p hp)) n

theorem homology_recentered (p : E) (hp : ‖p‖ < 1) (n : ℕ) :
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (recenteredSphere E p hp)) = 𝟙 _ := by
  change (CoefficientRadialPair.F R n).map
    (TopCat.ofHom (shiftedInclusion E p hp) ≫ TopCat.ofHom (radialNormalize E)) = _
  rw [Functor.map_comp, ← homology_shift, ← Functor.map_comp]
  have h : TopCat.ofHom (unitSphereInclusion E) ≫ TopCat.ofHom (radialNormalize E) = 𝟙 (TopCat.of (UnitSphere E)) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact radialNormalize_unitSphereInclusion E z
  rw [h, CategoryTheory.Functor.map_id]

theorem homology_betweenCenters (p q : E) (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) (n : ℕ) :
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (shiftedInclusion E p hp)) =
      (CoefficientRadialPair.F R n).map (TopCat.ofHom (shiftedInclusion E q hq)) :=
  (homology_shift E R p hp n).symm.trans (homology_shift E R q hq n)

def integral_example (p : EuclideanSpace ℝ (Fin 2)) (hp : ‖p‖ < 1) := homology_recentered _ ℤ p hp 1
def rational_example (p : EuclideanSpace ℝ (Fin 3)) (hp : ‖p‖ < 1) := homology_recentered _ ℚ p hp 2
#print axioms centerFamily
#print axioms betweenCenters
#print axioms homology_betweenCenters
#print axioms avoid_zero
#print axioms shiftHomotopy
#print axioms homology_shift
#print axioms homology_recentered
#print axioms integral_example
#print axioms rational_example
end ConstructionTargets.CoefficientMovingSphereCenter
