import ConstructionTargets.CoefficientNeighborhoodLocal
import Mathlib.Geometry.Manifold.ChartedSpace
noncomputable section
namespace ConstructionTargets.CoefficientChartPair
open CategoryTheory CategoryTheory.Limits
open CoefficientRadialPair CoefficientNeighborhoodLocal
variable (R : Type) [CommRing R]
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def homeoMap (e : X ≃ₜ Y) : C(X,Y) := ⟨e, e.continuous⟩
def deletedMap (e : X ≃ₜ Y) (x : X) :=
  pairMap R (deleted x) (deleted (e x)) (homeoMap e) (fun _ hy h => hy (e.injective h))

def deletedInverse (e : X ≃ₜ Y) (x : X) :=
  pairMap R (deleted (e x)) (deleted x) (homeoMap e.symm) (fun y hy h => hy (by
    change e.symm y = x at h
    exact (e.apply_symm_apply y).symm.trans (congrArg e h)))

theorem pair_inverse_right (e : X ≃ₜ Y) (x : X) : deletedMap R e x ≫ deletedInverse R e x = 𝟙 _ := by
  rw [deletedMap, deletedInverse, ← CoefficientPairNaturality.pair_comp]
  have h : (homeoMap e.symm).comp (homeoMap e) = ContinuousMap.id X := by ext y; exact e.symm_apply_apply y
  simpa only [h] using CoefficientPairNaturality.pair_id R (deleted x)

theorem pair_inverse_left (e : X ≃ₜ Y) (x : X) : deletedInverse R e x ≫ deletedMap R e x = 𝟙 _ := by
  rw [deletedMap, deletedInverse, ← CoefficientPairNaturality.pair_comp]
  have h : (homeoMap e).comp (homeoMap e.symm) = ContinuousMap.id Y := by ext y; exact e.apply_symm_apply y
  simpa only [h] using CoefficientPairNaturality.pair_id R (deleted (e x))

def pairIso (e : X ≃ₜ Y) (x : X) :
    CoefficientRelativeSmall.relativeChains R (deleted x) ≅ CoefficientRelativeSmall.relativeChains R (deleted (e x)) where
  hom := deletedMap R e x
  inv := deletedInverse R e x
  hom_inv_id := pair_inverse_right R e x
  inv_hom_id := pair_inverse_left R e x

def homologyIso (e : X ≃ₜ Y) (x : X) (n : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso (pairIso R e x)

variable (d : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
def chartHomeo (x : M) := (chartAt (EuclideanSpace ℝ (Fin d)) x).toHomeomorphSourceTarget

def sourcePoint (x : M) : (chartAt (EuclideanSpace ℝ (Fin d)) x).source := ⟨x, mem_chart_source _ x⟩

theorem chart_deleted_iff (x : M) (y : (chartAt (EuclideanSpace ℝ (Fin d)) x).source) :
    y ≠ sourcePoint d x ↔ chartHomeo d x y ≠ chartHomeo d x (sourcePoint d x) :=
  (chartHomeo d x).injective.ne_iff.symm

def chartPairIso (x : M) := pairIso R (chartHomeo d x) (sourcePoint d x)
def chartHomologyIso (x : M) (n : ℕ) := homologyIso R (chartHomeo d x) (sourcePoint d x) n

theorem source_member (x : M) : x ∈ (chartAt (EuclideanSpace ℝ (Fin d)) x).source := mem_chart_source _ x

theorem target_member (x : M) : (chartAt (EuclideanSpace ℝ (Fin d)) x) x ∈
    (chartAt (EuclideanSpace ℝ (Fin d)) x).target :=
  (chartAt (EuclideanSpace ℝ (Fin d)) x).map_source (source_member d x)

theorem chart_value (x : M) (y : (chartAt (EuclideanSpace ℝ (Fin d)) x).source) :
    (chartHomeo d x y).val = (chartAt (EuclideanSpace ℝ (Fin d)) x) y.val := rfl

theorem source_deleted (x : M) : deleted (sourcePoint d x) =
    localDeleted (chartAt (EuclideanSpace ℝ (Fin d)) x).source x := by
  ext y
  simp only [deleted, localDeleted, Set.mem_setOf_eq, ne_eq, Subtype.ext_iff, sourcePoint]

theorem target_deleted (x : M) : deleted (chartHomeo d x (sourcePoint d x)) =
    localDeleted (chartAt (EuclideanSpace ℝ (Fin d)) x).target
      ((chartAt (EuclideanSpace ℝ (Fin d)) x) x) := by
  ext y
  simp only [deleted, localDeleted, Set.mem_setOf_eq, ne_eq, Subtype.ext_iff, chart_value, sourcePoint]

theorem chart_projection (x : M) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (deleted (sourcePoint d x)))).f n ≫
      (chartPairIso R d x).hom.f n =
    (absoluteMap R (homeoMap (chartHomeo d x))).f n ≫
      (cokernel.π (CoefficientRelativeSmall.subspaceMap R
        (deleted (chartHomeo d x (sourcePoint d x))))).f n :=
  CoefficientRadialPair.projection_degree R (deleted (sourcePoint d x)) (deleted (chartHomeo d x (sourcePoint d x))) (homeoMap (chartHomeo d x)) (fun _ hy h => hy ((chartHomeo d x).injective h)) n

theorem chart_inverse_projection (x : M) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R
        (deleted (chartHomeo d x (sourcePoint d x))))).f n ≫
      (chartPairIso R d x).inv.f n =
    (absoluteMap R (homeoMap (chartHomeo d x).symm)).f n ≫
      (cokernel.π (CoefficientRelativeSmall.subspaceMap R (deleted (sourcePoint d x)))).f n :=
  CoefficientRadialPair.projection_degree R (deleted (chartHomeo d x (sourcePoint d x))) (deleted (sourcePoint d x)) (homeoMap (chartHomeo d x).symm) (fun y hy h => hy (by
    change (chartHomeo d x).symm y = sourcePoint d x at h
    exact ((chartHomeo d x).apply_symm_apply y).symm.trans (congrArg (chartHomeo d x) h))) n

theorem chart_forward (x : M) (n : ℕ) : (chartHomologyIso R d x n).hom =
    HomologicalComplex.homologyMap (deletedMap R (chartHomeo d x) (sourcePoint d x)) n := rfl

theorem chart_inverse_left (x : M) (n : ℕ) :
    (chartHomologyIso R d x n).inv ≫ (chartHomologyIso R d x n).hom = 𝟙 _ :=
  (chartHomologyIso R d x n).inv_hom_id

theorem chart_inverse_right (x : M) (n : ℕ) :
    (chartHomologyIso R d x n).hom ≫ (chartHomologyIso R d x n).inv = 𝟙 _ :=
  (chartHomologyIso R d x n).hom_inv_id

def integral_chart (m n : ℕ) (x : EuclideanSpace ℝ (Fin (m+2))) := chartHomologyIso ℤ (m+2) x n
def rational_chart (m n : ℕ) (x : EuclideanSpace ℝ (Fin (m+2))) := chartHomologyIso ℚ (m+2) x n
#print axioms pair_inverse_right
#print axioms pair_inverse_left
#print axioms chartPairIso
#print axioms chart_deleted_iff
#print axioms source_member
#print axioms target_member
#print axioms chart_value
#print axioms source_deleted
#print axioms target_deleted
#print axioms chart_projection
#print axioms chart_inverse_projection
#print axioms chart_forward
#print axioms chart_inverse_left
#print axioms chart_inverse_right
#print axioms integral_chart
#print axioms rational_chart
end ConstructionTargets.CoefficientChartPair
