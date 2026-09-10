import ConstructionTargets.CoefficientChartBoundaryNeighborhood
noncomputable section
namespace ConstructionTargets.CoefficientScaledBoundaryNormalization
open CategoryTheory PuncturedNormedSpaceRadialEquivalence CoefficientCompactBoundaryMotion
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
def scaled (r : ℝ) : C(UnitSphere E,E) := ⟨fun z => r • z.val, by fun_prop⟩
theorem norm_scaled (r : ℝ) (hr : 0 < r) (z : UnitSphere E) : ‖scaled E r z‖ = r := by
  change ‖r • z.val‖ = r
  rw [norm_smul, Real.norm_of_nonneg hr.le]
  have hz : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.property
  rw [hz,mul_one]
theorem gap (r : ℝ) (hr : 0 < r) : ∀ z, r ≤ ‖scaled E r z - 0‖ := by
  intro z; simp only [sub_zero, norm_scaled E r hr z, le_refl]
theorem avoids (r : ℝ) (hr : 0 < r) : ∀ z, scaled E r z ≠ 0 := by
  intro z hz
  have hn := norm_scaled E r hr z
  rw [hz,norm_zero] at hn
  exact hr.ne hn

def recentered (r : ℝ) (hr : 0 < r) (p : E) (hp : ‖p‖ < r) :=
  boundaryMap (scaled E r) p (new_center (scaled E r) 0 p r (gap E r hr) (by simpa using hp))
def normalized (r : ℝ) (hr : 0 < r) (p : E) (hp : ‖p‖ < r) :=
  (radialNormalize E).comp (recentered E r hr p hp)
theorem normalized_value (r : ℝ) (hr : 0 < r) (p : E) (hp : ‖p‖ < r) (z : UnitSphere E) :
    (normalized E r hr p hp z).val = NormedSpace.normalize (r • z.val - p) := rfl

theorem centered_identity (r : ℝ) (hr : 0 < r) :
    radialBoundary (scaled E r) 0 (avoids E r hr) = ContinuousMap.id (UnitSphere E) := by
  apply ContinuousMap.ext; intro z; apply Subtype.ext
  change NormedSpace.normalize (r • z.val - 0) = z.val
  rw [sub_zero, NormedSpace.normalize_smul_of_pos hr]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (by simpa only [Metric.mem_sphere, dist_zero_right] using z.property)

variable (R : Type) [CommRing R]
theorem homology_identity (r : ℝ) (hr : 0 < r) (p : E) (hp : ‖p‖ < r) (n : ℕ) :
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (normalized E r hr p hp)) = 𝟙 _ := by
  have h := radial_homology_eq R (scaled E r) 0 p (avoids E r hr) r (gap E r hr) (by simpa using hp) n
  rw [centered_identity E r hr] at h
  exact h.symm.trans ((CoefficientRadialPair.F R n).map_id _)

def radialIso (n : ℕ) := CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv R
  (unitSphereHomotopyEquivPuncturedSpace E).symm n

theorem forward_inverse (r : ℝ) (hr : 0 < r) (p : E) (hp : ‖p‖ < r) (n : ℕ) :
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (recentered E r hr p hp)) = (radialIso E R n).inv := by
  apply (cancel_mono (radialIso E R n).hom).mp
  rw [Iso.inv_hom_id]
  change (CoefficientRadialPair.F R n).map (TopCat.ofHom (recentered E r hr p hp)) ≫
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (radialNormalize E)) = _
  rw [← CategoryTheory.Functor.map_comp]
  exact homology_identity E R r hr p hp n

def boundaryIso (r : ℝ) (hr : 0 < r) (p : E) (hp : ‖p‖ < r) (n : ℕ) :
    (CoefficientRadialPair.F R n).obj (TopCat.of (UnitSphere E)) ≅
      (CoefficientRadialPair.F R n).obj (TopCat.of (PuncturedSpace E)) :=
  { (radialIso E R n).symm with
    hom := (CoefficientRadialPair.F R n).map (TopCat.ofHom (recentered E r hr p hp))
    hom_inv_id := by rw [forward_inverse]; exact (radialIso E R n).inv_hom_id
    inv_hom_id := by rw [forward_inverse]; exact (radialIso E R n).hom_inv_id }

theorem inverse_right (r : ℝ) (hr : 0 < r) (p : E) (hp : ‖p‖ < r) (n : ℕ) :
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (recentered E r hr p hp)) ≫
      (CoefficientRadialPair.F R n).map (TopCat.ofHom (radialNormalize E)) = 𝟙 _ := by
  rw [forward_inverse]
  exact (radialIso E R n).inv_hom_id

theorem inverse_left (r : ℝ) (hr : 0 < r) (p : E) (hp : ‖p‖ < r) (n : ℕ) :
    (CoefficientRadialPair.F R n).map (TopCat.ofHom (radialNormalize E)) ≫
      (CoefficientRadialPair.F R n).map (TopCat.ofHom (recentered E r hr p hp)) = 𝟙 _ := by
  rw [forward_inverse]
  exact (radialIso E R n).hom_inv_id

def integral_example (r : ℝ) (hr : 0 < r) (p : EuclideanSpace ℝ (Fin 2)) (hp : ‖p‖ < r) := boundaryIso _ ℤ r hr p hp 1
def rational_example (r : ℝ) (hr : 0 < r) (p : EuclideanSpace ℝ (Fin 3)) (hp : ‖p‖ < r) := boundaryIso _ ℚ r hr p hp 2
#print axioms inverse_right
#print axioms inverse_left
#print axioms norm_scaled
#print axioms avoids
#print axioms centered_identity
#print axioms homology_identity
#print axioms forward_inverse
#print axioms boundaryIso
#print axioms integral_example
#print axioms rational_example
end ConstructionTargets.CoefficientScaledBoundaryNormalization
