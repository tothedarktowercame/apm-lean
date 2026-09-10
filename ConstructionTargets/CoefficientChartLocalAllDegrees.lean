import ConstructionTargets.CoefficientChartLocal
noncomputable section
namespace ConstructionTargets.CoefficientChartLocalAllDegrees
open CategoryTheory
open CoefficientNeighborhoodLocal CoefficientChartPair CoefficientChartLocal
variable (R : Type) [CommRing R]
variable (m : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
def comparison (x : M) (n : ℕ) :
    H R (deleted x) n ≅ H R (deleted (0 : E m)) n :=
  (inclusionIso R (chartAt (E m) x).source x (chartAt (E m) x).open_source
    (source_member (m+2) x) n).symm ≪≫
  (sourceTransport R m x n).symm ≪≫
  homologyIso R (pointedChart m x) (sourcePoint (m+2) x) n ≪≫
  targetTransport R m x n ≪≫
  inclusionIso R (pointedTarget m x) 0 (pointed_open m x) (pointed_zero m x) n

theorem forward (x : M) (n : ℕ) : (comparison R m x n).hom =
    (inclusionIso R (chartAt (E m) x).source x (chartAt (E m) x).open_source
      (source_member (m+2) x) n).inv ≫
    (sourceTransport R m x n).inv ≫
    HomologicalComplex.homologyMap
      (deletedMap R (pointedChart m x) (sourcePoint (m+2) x)) n ≫
    (targetTransport R m x n).hom ≫
    HomologicalComplex.homologyMap (inclusionMap R (pointedTarget m x) 0) n := rfl

theorem inverse_left (x : M) (n : ℕ) :
    (comparison R m x n).inv ≫ (comparison R m x n).hom = 𝟙 _ :=
  (comparison R m x n).inv_hom_id

theorem inverse_right (x : M) (n : ℕ) :
    (comparison R m x n).hom ≫ (comparison R m x n).inv = 𝟙 _ :=
  (comparison R m x n).hom_inv_id

theorem normalization_factorization (x : M) :
    comparison R m x (m+2) ≪≫ CoefficientModelLocal.localIso R m =
      CoefficientChartLocal.localIso R m x := by
  apply Iso.ext
  rfl

theorem generator_image (x : M) :
    (comparison R m x (m+2)).hom.hom (CoefficientChartLocal.generator R m x) =
      CoefficientModelLocal.generator R m := by
  apply (ConcreteCategory.bijective_of_isIso (CoefficientModelLocal.localIso R m).hom).1
  have h := CoefficientChartLocal.generator_normalization R m x
  change (CoefficientModelLocal.localIso R m).hom.hom
    ((comparison R m x (m+2)).hom.hom (CoefficientChartLocal.generator R m x)) = 1 at h
  rw [h]
  exact (CoefficientModelLocal.generator_normalization R m).symm

#print axioms comparison
#print axioms forward
#print axioms inverse_left
#print axioms inverse_right
#print axioms normalization_factorization
#print axioms generator_image
end ConstructionTargets.CoefficientChartLocalAllDegrees
