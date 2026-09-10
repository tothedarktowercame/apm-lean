import ConstructionTargets.CoefficientDistinguishedChart
noncomputable section
namespace ConstructionTargets.CoefficientDistinguishedTargetNormalization
open CategoryTheory
open CoefficientOverlapPair CoefficientDistinguishedChart CoefficientNeighborhoodLocal
variable (R : Type) [CommRing R] (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
theorem inclusion_square (x : M) :
    (targetPair m R x).hom ≫ inclusionMap R (CoefficientChartLocal.pointedTarget m x) 0 =
      inclusionMap R (image m x (chartAt (E m) x).source x) 0 := by
  unfold targetPair CoefficientOverlapNormalization.pairHomeo inclusionMap
  dsimp only
  rw [← CoefficientPairNaturality.pair_comp]
  rfl

theorem homology_square (x : M) (n : ℕ) :
    (targetHomologyIso m R x n).hom ≫
      HomologicalComplex.homologyMap (inclusionMap R (CoefficientChartLocal.pointedTarget m x) 0) n =
    HomologicalComplex.homologyMap (inclusionMap R (image m x (chartAt (E m) x).source x) 0) n := by
  rw [target_homology_forward]
  erw [← HomologicalComplex.homologyMap_comp]
  rw [inclusion_square]

def zero_mem (x : M) : 0 ∈ image m x (chartAt (E m) x).source x := by
  rw [image_eq]
  exact CoefficientChartLocal.pointed_zero m x

theorem normalization_square (x : M) :
    targetHomologyIso m R x (m+2) ≪≫
      modelNormalization R m (CoefficientChartLocal.pointedTarget m x)
        (CoefficientChartLocal.pointed_open m x) (CoefficientChartLocal.pointed_zero m x) =
      modelNormalization R m (image m x (chartAt (E m) x).source x)
        (image_open m x _ x) (zero_mem m x) := by
  apply Iso.ext
  change (targetHomologyIso m R x (m+2)).hom ≫
    (HomologicalComplex.homologyMap (inclusionMap R (CoefficientChartLocal.pointedTarget m x) 0) (m+2) ≫
      (CoefficientModelLocal.localIso R m).hom) =
    HomologicalComplex.homologyMap (inclusionMap R (image m x (chartAt (E m) x).source x) 0) (m+2) ≫
      (CoefficientModelLocal.localIso R m).hom
  rw [← Category.assoc, homology_square]
  rfl
#print axioms inclusion_square
#print axioms homology_square
#print axioms normalization_square
end ConstructionTargets.CoefficientDistinguishedTargetNormalization
