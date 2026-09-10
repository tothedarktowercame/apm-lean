import ConstructionTargets.CoefficientChartBallTransport
noncomputable section
namespace ConstructionTargets.CoefficientChartBallNormalization
open CategoryTheory CoefficientOverlapPair CoefficientNeighborhoodLocal
open CoefficientChartBallTransport CoefficientOverlapNormalization
variable (R : Type) [CommRing R] (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
variable (a b y : M) (hy : y ∈ common m a b)

theorem coordinate_factorization :
    (chartPair R m a (common m a b) (common_open m a b) Set.inter_subset_left y hy).hom ≫
      inclusionMap R (image m a (common m a b) y) 0 = coordinateMap m a b y hy R := by
  unfold chartPair pairHomeo inclusionMap coordinateMap
  dsimp only
  rw [← CoefficientPairNaturality.pair_comp]
  rfl

theorem coordinate_homology (n : ℕ) :
    HomologicalComplex.homologyMap
      (chartPair R m a (common m a b) (common_open m a b) Set.inter_subset_left y hy).hom n ≫
      HomologicalComplex.homologyMap (inclusionMap R (image m a (common m a b) y) 0) n =
      HomologicalComplex.homologyMap (coordinateMap m a b y hy R) n := by
  rw [← HomologicalComplex.homologyMap_comp, coordinate_factorization]
  rfl

variable [T2Space M]
theorem inclusion_normalization :
    HomologicalComplex.homologyMap (inclusionMap R (common m a b) y) (m+2) ≫
      (normalization R m a (common m a b) (common_open m a b) Set.inter_subset_left y hy).hom =
    HomologicalComplex.homologyMap (coordinateMap m a b y hy R) (m+2) ≫
      (CoefficientModelLocal.localIso R m).hom := by
  erw [← coordinate_homology R m a b y hy (m+2), Category.assoc]
  unfold normalization ambientIso modelNormalization
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
  rw [← inclusionIso_hom R (common m a b) y (common_open m a b) hy (m+2)]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_assoc]
  rfl

variable (x : M) (hx : x ∈ common m a b)
  (hp : ‖chartAt (E m) a y - chartAt (E m) a x‖ < r m a b x hx)
theorem ambient_normalization :
    CoefficientBallBoundaryLift.lift R m (r m a b x hx)
      (CoefficientChartBoundaryNeighborhood.radius_pos m a b x hx) ≫
    HomologicalComplex.homologyMap (relativeMap m a b x hx y hp R) (m+2) ≫
    HomologicalComplex.homologyMap (inclusionMap R (common m a b) y) (m+2) ≫
      (normalization R m a (common m a b) (common_open m a b) Set.inter_subset_left y hy).hom =
    (CoefficientSphereAntipodal.normalization R m).hom := by
  rw [inclusion_normalization]
  exact lifted_normalization m a b x hx y hy hp R

theorem nearby_normalization : ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
    V ⊆ common m a b ∧ ∀ z ∈ V, ∃ hz : z ∈ common m a b,
    ∃ hpz : ‖chartAt (E m) a z - chartAt (E m) a x‖ < r m a b x hx,
    CoefficientBallBoundaryLift.lift R m (r m a b x hx)
      (CoefficientChartBoundaryNeighborhood.radius_pos m a b x hx) ≫
    HomologicalComplex.homologyMap (relativeMap m a b x hx z hpz R) (m+2) ≫
    HomologicalComplex.homologyMap (inclusionMap R (common m a b) z) (m+2) ≫
      (normalization R m a (common m a b) (common_open m a b) Set.inter_subset_left z hz).hom =
    (CoefficientSphereAntipodal.normalization R m).hom := by
  obtain ⟨V,hV,hxV,hsub,hnear⟩ :=
    CoefficientChartBoundaryNeighborhood.boundary_neighborhood m a b x hx R
  refine ⟨V,hV,hxV,hsub,fun z hz => ?_⟩
  exact ⟨hsub hz,(hnear z hz).1,ambient_normalization R m a b z (hsub hz) x hx (hnear z hz).1⟩

#print axioms nearby_normalization
#print axioms coordinate_factorization
#print axioms coordinate_homology
#print axioms inclusion_normalization
#print axioms ambient_normalization
end ConstructionTargets.CoefficientChartBallNormalization
