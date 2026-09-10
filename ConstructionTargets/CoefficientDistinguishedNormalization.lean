import ConstructionTargets.CoefficientDistinguishedTargetNormalization
noncomputable section
namespace ConstructionTargets.CoefficientDistinguishedNormalization
open CategoryTheory
open CoefficientOverlapPair CoefficientOverlapNormalization CoefficientDistinguishedChart
open CoefficientNeighborhoodLocal CoefficientChartPair CoefficientRadialPair
variable (R : Type) [CommRing R]
theorem transport {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (p : X) (A : Set X) (B : Set Y)
    (hA : deleted p = A) (hB : deleted (e p) = B)
    (h : ∀ y, e y ∈ B ↔ y ∈ A) (n : ℕ) :
    HomologicalComplex.homologyMap (pairHomeo R e A B h).hom n =
      (eqToIso (congrArg (fun S => CoefficientChartLocal.H R S n) hA)).inv ≫
      (homologyIso R e p n).hom ≫
      (eqToIso (congrArg (fun S => CoefficientChartLocal.H R S n) hB)).hom := by
  subst A; subst B
  simp only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom, Category.id_comp]
  rfl
variable (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
theorem chart_square (x : M) (n : ℕ) :
    HomologicalComplex.homologyMap
      (chartPair R m x (chartAt (E m) x).source (chartAt (E m) x).open_source
        Set.Subset.rfl x (mem_chart_source (E m) x)).hom n ≫
      (targetHomologyIso m R x n).hom =
    (CoefficientChartLocal.sourceTransport R m x n).inv ≫
      (homologyIso R (CoefficientChartLocal.pointedChart m x) (sourcePoint (m+2) x) n).hom ≫
      (CoefficientChartLocal.targetTransport R m x n).hom := by
  rw [target_homology_forward]
  erw [← HomologicalComplex.homologyMap_comp]
  unfold chartPair targetPair pairHomeo
  dsimp only
  rw [← CoefficientPairNaturality.pair_comp]
  have he : (homeoMap (targetHomeo m x)).comp
      (homeoMap (pointed m x (chartAt (E m) x).source (chartAt (E m) x).open_source Set.Subset.rfl x)) =
      homeoMap (CoefficientChartLocal.pointedChart m x) := by
    exact congrArg homeoMap (pointed_eq m x)
  simp only [he]
  have hh : ∀ y, CoefficientChartLocal.pointedChart m x y ∈
      localDeleted (CoefficientChartLocal.pointedTarget m x) 0 ↔
      y ∈ localDeleted (chartAt (E m) x).source x := by
    rw [← source_deleted (m+2) x, ← CoefficientChartLocal.pointed_deleted m x]
    intro y
    exact not_congr (CoefficientChartLocal.pointedChart m x).injective.eq_iff
  exact transport R _ _ _ _ (source_deleted (m+2) x) (CoefficientChartLocal.pointed_deleted m x) hh n
variable [T2Space M]
theorem distinguished (x : M) :
    normalization R m x (chartAt (E m) x).source (chartAt (E m) x).open_source
      Set.Subset.rfl x (mem_chart_source (E m) x) = CoefficientChartLocal.localIso R m x := by
  apply Iso.ext
  unfold normalization ambientIso CoefficientChartLocal.localIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
  have ht := congrArg Iso.hom (CoefficientDistinguishedTargetNormalization.normalization_square R m x)
  dsimp only [Iso.trans_hom] at ht
  rw [← ht]
  simp only [Category.assoc]
  have hc := congrArg (fun q =>
    (inclusionIso R (chartAt (E m) x).source x (chartAt (E m) x).open_source
      (mem_chart_source (E m) x) (m+2)).inv ≫ q ≫
    (modelNormalization R m (CoefficientChartLocal.pointedTarget m x)
      (CoefficientChartLocal.pointed_open m x) (CoefficientChartLocal.pointed_zero m x)).hom)
    (chart_square R m x (m+2))
  simpa only [Category.assoc] using hc
theorem distinguished_forward (x : M) :
    (normalization R m x (chartAt (E m) x).source (chartAt (E m) x).open_source
      Set.Subset.rfl x (mem_chart_source (E m) x)).hom =
    (CoefficientChartLocal.localIso R m x).hom := congrArg Iso.hom (distinguished R m x)
#print axioms CoefficientOverlapNormalization.ambient_forward
#print axioms CoefficientOverlapNormalization.ambient_inverse_left
#print axioms CoefficientOverlapNormalization.ambient_inverse_right
#print axioms CoefficientOverlapNormalization.left_forward
#print axioms CoefficientOverlapNormalization.right_forward
#print axioms CoefficientOverlapNormalization.geometric_comparison
#print axioms CoefficientOverlapNormalization.normalization_comparison
#print axioms distinguished_forward
#print axioms distinguished
#print axioms transport
#print axioms chart_square
end ConstructionTargets.CoefficientDistinguishedNormalization
