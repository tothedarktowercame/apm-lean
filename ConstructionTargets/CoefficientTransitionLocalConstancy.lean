import ConstructionTargets.CoefficientSecondChartBoundaryMotion
import ConstructionTargets.CoefficientChartTransitionUnit
noncomputable section
namespace ConstructionTargets.CoefficientTransitionLocalConstancy
open CategoryTheory CoefficientOverlapPair CoefficientOverlapNormalization CoefficientNeighborhoodLocal
open CoefficientChartBallTransport CoefficientChartBoundaryNeighborhood CoefficientSecondChartBoundary
variable (R : Type) [CommRing R] (m : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]

 theorem inclusion_normalization (a : M) (U : Set M) (hU : IsOpen U)
    (h : U ⊆ (chartAt (E m) a).source) (y : M) (hy : y ∈ U) :
    HomologicalComplex.homologyMap (inclusionMap R U y) (m+2) ≫
      (normalization R m a U hU h y hy).hom =
    HomologicalComplex.homologyMap (chartPair R m a U hU h y hy).hom (m+2) ≫
      HomologicalComplex.homologyMap (inclusionMap R (image m a U y) 0) (m+2) ≫
      (CoefficientModelLocal.localIso R m).hom := by
  unfold normalization ambientIso modelNormalization
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
  rw [← inclusionIso_hom R U y hU hy (m+2)]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_assoc]
  rfl

variable (a b x : M) (hx : x ∈ common m a b) (y : M) (hy : y ∈ common m a b)
    (hp : ‖chartAt (E m) a y - chartAt (E m) a x‖ < r m a b x hx)
omit [T2Space M] in
theorem second_factorization : relativeMap m a b x hx y hp R ≫
    (chartPair R m b (common m a b) (common_open m a b) Set.inter_subset_right y hy).hom ≫
    inclusionMap R (image m b (common m a b) y) 0 = secondRelative R m a b x hx y hy hp := by
  unfold relativeMap chartPair pairHomeo inclusionMap secondRelative
  dsimp only
  rw [← CoefficientPairNaturality.pair_comp, ← CoefficientPairNaturality.pair_comp]
  rfl

def lifted := CoefficientBallBoundaryLift.lift R m (r m a b x hx) (radius_pos m a b x hx) ≫
  HomologicalComplex.homologyMap (relativeMap m a b x hx y hp R) (m+2) ≫
  HomologicalComplex.homologyMap (inclusionMap R (common m a b) y) (m+2)

theorem lifted_left : lifted R m a b x hx y hp ≫
    (CoefficientChartTransitionUnit.chartNormalization R m a y hy.1).hom =
    (CoefficientSphereAntipodal.normalization R m).hom := by
  rw [← CoefficientChartTransitionUnit.left_restriction R m a b y hy]
  simpa only [lifted, Category.assoc] using
    CoefficientChartBallNormalization.ambient_normalization R m a b y hy x hx hp

theorem lifted_right : lifted R m a b x hx y hp ≫
    (CoefficientChartTransitionUnit.chartNormalization R m b y hy.2).hom =
    CoefficientBallBoundaryLift.lift R m (r m a b x hx) (radius_pos m a b x hx) ≫
      HomologicalComplex.homologyMap (secondRelative R m a b x hx y hy hp) (m+2) ≫
      (CoefficientModelLocal.localIso R m).hom := by
  rw [← CoefficientChartTransitionUnit.right_restriction R m a b y hy]
  unfold lifted
  simp only [Category.assoc]
  unfold rightNormalization
  erw [inclusion_normalization R m b (common m a b) (common_open m a b) Set.inter_subset_right y hy]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f (m+2))
    (second_factorization R m a b x hx y hy hp)
  dsimp only at h
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  erw [← Category.assoc (HomologicalComplex.homologyMap (relativeMap m a b x hx y hp R) (m+2)),
    ← Category.assoc (HomologicalComplex.homologyMap (relativeMap m a b x hx y hp R) (m+2) ≫ _), h]
  rfl

open CoefficientChartTransitionUnit

theorem comparison_lift : (CoefficientSphereAntipodal.normalization R m).hom ≫
    (comparison R m a b y hy.1 hy.2).hom =
    lifted R m a b x hx y hp ≫ (chartNormalization R m b y hy.2).hom := by
  rw [← lifted_left R m a b x hx y hy hp]
  simp only [comparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]

theorem locally_constant (a b x : M) (hx : x ∈ common m a b) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ common m a b ∧
      ∀ y ∈ V, ∃ hy : y ∈ common m a b,
        transitionUnit R m a b y hy.1 hy.2 = transitionUnit R m a b x hx.1 hx.2 := by
  obtain ⟨V, hV, hxV, hsub, heq⟩ :=
    CoefficientSecondChartBoundaryMotion.nearby_normalized R m a b x hx
  refine ⟨V, hV, hxV, hsub, ?_⟩
  intro y hyV
  obtain ⟨hy, hp, heq⟩ := heq y hyV
  refine ⟨hy, ?_⟩
  have hcomp : (comparison R m a b y hy.1 hy.2).hom =
      (comparison R m a b x hx.1 hx.2).hom := by
    apply (cancel_epi (CoefficientSphereAntipodal.normalization R m).hom).mp
    rw [comparison_lift R m a b x hx y hy hp,
      comparison_lift R m a b x hx x hx
        (CoefficientSecondChartBoundaryMotion.center_bound m a b x hx)]
    rw [lifted_right R m a b x hx y hy hp,
      lifted_right R m a b x hx x hx
        (CoefficientSecondChartBoundaryMotion.center_bound m a b x hx)]
    exact heq
  apply Units.ext
  exact congrArg (fun f => f.hom 1) hcomp

#print axioms inclusion_normalization
#print axioms second_factorization
#print axioms lifted_left
#print axioms lifted_right
#print axioms comparison_lift
#print axioms locally_constant
end ConstructionTargets.CoefficientTransitionLocalConstancy
