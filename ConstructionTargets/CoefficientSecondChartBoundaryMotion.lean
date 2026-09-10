import ConstructionTargets.CoefficientSecondChartBoundary
noncomputable section
namespace ConstructionTargets.CoefficientSecondChartBoundaryMotion
open CategoryTheory CoefficientOverlapPair CoefficientChartBoundaryNeighborhood
open CoefficientChartBallTransport CoefficientSecondChartBoundary CoefficientRadialPair
variable (R : Type) [CommRing R] (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
variable (a b x : M) (hx : x ∈ common m a b)
theorem center_bound : ‖chartAt (E m) a x - chartAt (E m) a x‖ < r m a b x hx := by
  simpa using radius_pos m a b x hx

theorem sphere_identification (y : M) (hy : y ∈ common m a b)
    (hp : ‖chartAt (E m) a y - chartAt (E m) a x‖ < r m a b x hx)
    (ha : ∀ z, mappedBoundary m a b x hx z ≠ chartAt (E m) b y - chartAt (E m) b x) :
    sphereMap m a b x hx y hy hp = CoefficientCompactBoundaryMotion.boundaryMap
      (mappedBoundary m a b x hx) (chartAt (E m) b y - chartAt (E m) b x) ha := by
  apply ContinuousMap.ext
  intro z
  exact Subtype.ext (sphere_value m a b x hx y hy hp z)

theorem center_identification :
    sphereMap m a b x hx x hx (center_bound m a b x hx) =
      CoefficientCompactBoundaryMotion.boundaryMap (mappedBoundary m a b x hx) 0
        (mapped_avoids m a b x hx) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  simpa [CoefficientCompactBoundaryMotion.boundaryMap] using sphere_value m a b x hx x hx (center_bound m a b x hx) z

theorem nearby_homology : ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ common m a b ∧
    ∀ y ∈ V, ∃ hy : y ∈ common m a b,
      ∃ hp : ‖chartAt (E m) a y - chartAt (E m) a x‖ < r m a b x hx,
      ∀ n : ℕ, (F R n).map (TopCat.ofHom (sphereMap m a b x hx y hy hp)) =
        (F R n).map (TopCat.ofHom (sphereMap m a b x hx x hx (center_bound m a b x hx))) := by
  obtain ⟨V,hV,hxV,hsub,hnear⟩ := boundary_neighborhood m a b x hx R
  refine ⟨V,hV,hxV,hsub,fun y hyV => ?_⟩
  obtain ⟨hp,ha,hm⟩ := hnear y hyV
  refine ⟨hsub hyV,hp,fun n => ?_⟩
  rw [sphere_identification m a b x hx y (hsub hyV) hp ha, center_identification]
  exact (hm n).symm

theorem nearby_normalized : ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ common m a b ∧
    ∀ y ∈ V, ∃ hy : y ∈ common m a b,
      ∃ hp : ‖chartAt (E m) a y - chartAt (E m) a x‖ < r m a b x hx,
      CoefficientBallBoundaryLift.lift R m (r m a b x hx) (radius_pos m a b x hx) ≫
        HomologicalComplex.homologyMap (secondRelative R m a b x hx y hy hp) (m+2) ≫
        (CoefficientModelLocal.localIso R m).hom =
      CoefficientBallBoundaryLift.lift R m (r m a b x hx) (radius_pos m a b x hx) ≫
        HomologicalComplex.homologyMap (secondRelative R m a b x hx x hx (center_bound m a b x hx)) (m+2) ≫
        (CoefficientModelLocal.localIso R m).hom := by
  obtain ⟨V,hV,hxV,hsub,hnear⟩ := nearby_homology R m a b x hx
  refine ⟨V,hV,hxV,hsub,fun y hyV => ?_⟩
  obtain ⟨hy,hp,hm⟩ := hnear y hyV
  refine ⟨hy,hp,?_⟩
  rw [normalized_connecting, normalized_connecting, hm (m+1)]
#print axioms sphere_identification
#print axioms center_identification
#print axioms nearby_homology
#print axioms nearby_normalized
end ConstructionTargets.CoefficientSecondChartBoundaryMotion
