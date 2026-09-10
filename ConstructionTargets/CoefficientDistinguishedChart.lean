import ConstructionTargets.CoefficientOverlapNormalization
noncomputable section
namespace ConstructionTargets.CoefficientDistinguishedChart
open CategoryTheory
open CoefficientOverlapPair
variable (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
theorem restricted_eq (x : M) : restricted m x (chartAt (E m) x).source = chartAt (E m) x := by
  apply OpenPartialHomeomorph.restr_eq_of_source_subset
  exact Set.Subset.rfl

theorem image_eq (x : M) : image m x (chartAt (E m) x).source x = CoefficientChartLocal.pointedTarget m x := by
  unfold image CoefficientChartLocal.pointedTarget CoefficientChartLocal.coordinate
  rw [restricted_eq]

def targetHomeo (x : M) := Homeomorph.setCongr (image_eq m x)

theorem pointed_eq (x : M) :
    (pointed m x (chartAt (E m) x).source (chartAt (E m) x).open_source Set.Subset.rfl x).trans
      (targetHomeo m x) = CoefficientChartLocal.pointedChart m x := by
  apply Homeomorph.ext
  intro y
  apply Subtype.ext
  rfl

theorem target_value (x : M) (y : image m x (chartAt (E m) x).source x) :
    (targetHomeo m x y).val = y.val := rfl

theorem inverse_pointed_eq (x : M) :
    (targetHomeo m x).symm.trans
      (pointed m x (chartAt (E m) x).source (chartAt (E m) x).open_source Set.Subset.rfl x).symm =
      (CoefficientChartLocal.pointedChart m x).symm := by
  exact congrArg Homeomorph.symm (pointed_eq m x)

variable (R : Type) [CommRing R]
def targetPair (x : M) := CoefficientOverlapNormalization.pairHomeo R (targetHomeo m x)
  (CoefficientNeighborhoodLocal.localDeleted (image m x (chartAt (E m) x).source x) 0)
  (CoefficientNeighborhoodLocal.localDeleted (CoefficientChartLocal.pointedTarget m x) 0)
  (fun _ => Iff.rfl)

theorem target_pair_inverse_left (x : M) : (targetPair m R x).inv ≫ (targetPair m R x).hom = 𝟙 _ :=
  (targetPair m R x).inv_hom_id

theorem target_pair_inverse_right (x : M) : (targetPair m R x).hom ≫ (targetPair m R x).inv = 𝟙 _ :=
  (targetPair m R x).hom_inv_id
def targetHomologyIso (x : M) (n : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso (targetPair m R x)
theorem target_homology_forward (x : M) (n : ℕ) : (targetHomologyIso m R x n).hom =
    HomologicalComplex.homologyMap (targetPair m R x).hom n := rfl
#print axioms targetHomologyIso
#print axioms target_homology_forward
#print axioms restricted_eq
#print axioms image_eq
#print axioms pointed_eq
#print axioms inverse_pointed_eq
#print axioms targetPair
#print axioms target_pair_inverse_left
#print axioms target_pair_inverse_right
end ConstructionTargets.CoefficientDistinguishedChart
