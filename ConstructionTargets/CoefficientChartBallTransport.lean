import ConstructionTargets.CoefficientBallBoundaryLift
import ConstructionTargets.CoefficientOverlapNormalization
noncomputable section
namespace ConstructionTargets.CoefficientChartBallTransport
open CategoryTheory CoefficientOverlapPair CoefficientChartBoundaryNeighborhood
open CoefficientRadialPair CoefficientNeighborhoodLocal
variable (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
variable (a b x : M) (hx : x ∈ common m a b)
abbrev r := radius m a b x hx

def ballMap : C(CoefficientBallBoundaryLift.Ball m (r m a b x hx), common m a b) :=
  (CoefficientChartPair.homeoMap (left m a b x).symm).comp
    ⟨fun z => ⟨z.val, radius_subset m a b x hx z.property⟩, by fun_prop⟩

theorem coordinate (z : CoefficientBallBoundaryLift.Ball m (r m a b x hx)) :
    chartAt (E m) a (ballMap m a b x hx z).val - chartAt (E m) a x = z.val := by
  exact congrArg Subtype.val ((left m a b x).apply_symm_apply
    ⟨z.val, radius_subset m a b x hx z.property⟩)

variable (y : M) (hy : y ∈ common m a b)
  (hp : ‖chartAt (E m) a y - chartAt (E m) a x‖ < r m a b x hx)
include hp in
theorem boundary_deleted : Set.MapsTo (ballMap m a b x hx)
    (CoefficientBallBoundaryLift.boundary m (r m a b x hx)) (localDeleted (common m a b) y) := by
  intro z hz he
  have hc := coordinate m a b x hx z
  rw [he] at hc
  have hn : ‖z.val‖ = r m a b x hx := hz
  rw [← hc] at hn
  exact (ne_of_lt hp) hn

variable (R : Type) [CommRing R]
def relativeMap := pairMap R _ _ (ballMap m a b x hx) (boundary_deleted m a b x hx y hp)

def coordinates : C(common m a b, E m) :=
  ⟨fun z => chartAt (E m) a z.val - chartAt (E m) a y,
    (((chartAt (E m) a).continuousOn.comp_continuous continuous_subtype_val
      (fun z => z.property.1))).sub continuous_const⟩

include hy in
theorem coordinates_deleted : Set.MapsTo (coordinates m a b y)
    (localDeleted (common m a b) y) (CoefficientModelLocal.puncture (m+2)) := by
  intro z hz he
  apply hz
  exact (chartAt (E m) a).injOn z.property.1 hy.1 (sub_eq_zero.mp he)

def coordinateMap := pairMap R _ _ (coordinates m a b y) (coordinates_deleted m a b y hy)

theorem coordinate_composite : (coordinates m a b y).comp (ballMap m a b x hx) =
    CoefficientBallBoundaryLift.recenter m (r m a b x hx)
      (chartAt (E m) a y - chartAt (E m) a x) := by
  apply ContinuousMap.ext
  intro z
  change chartAt (E m) a (ballMap m a b x hx z).val - chartAt (E m) a y = _
  have h := coordinate m a b x hx z
  change _ = z.val - (chartAt (E m) a y - chartAt (E m) a x)
  rw [← h]
  abel

theorem relative_square : relativeMap m a b x hx y hp R ≫ coordinateMap m a b y hy R =
    CoefficientBallBoundaryLift.relativeMap R m (r m a b x hx)
      (chartAt (E m) a y - chartAt (E m) a x) hp := by
  unfold relativeMap coordinateMap CoefficientBallBoundaryLift.relativeMap
  rw [← CoefficientPairNaturality.pair_comp]
  congr 1
  exact coordinate_composite m a b x hx y

theorem homology_square (n : ℕ) :
    HomologicalComplex.homologyMap (relativeMap m a b x hx y hp R) n ≫
      HomologicalComplex.homologyMap (coordinateMap m a b y hy R) n =
    HomologicalComplex.homologyMap (CoefficientBallBoundaryLift.relativeMap R m
      (r m a b x hx) (chartAt (E m) a y - chartAt (E m) a x) hp) n := by
  rw [← HomologicalComplex.homologyMap_comp, relative_square]

theorem lifted_normalization :
    CoefficientBallBoundaryLift.lift R m (r m a b x hx) (radius_pos m a b x hx) ≫
      HomologicalComplex.homologyMap (relativeMap m a b x hx y hp R) (m+2) ≫
      HomologicalComplex.homologyMap (coordinateMap m a b y hy R) (m+2) ≫
      (CoefficientModelLocal.localIso R m).hom =
    (CoefficientSphereAntipodal.normalization R m).hom := by
  rw [← Category.assoc (HomologicalComplex.homologyMap (relativeMap m a b x hx y hp R) (m+2)),
    homology_square]
  exact CoefficientBallBoundaryLift.normalization R m (r m a b x hx)
    (radius_pos m a b x hx) (chartAt (E m) a y - chartAt (E m) a x) hp

#print axioms lifted_normalization
#print axioms coordinate
#print axioms boundary_deleted
#print axioms coordinates_deleted
#print axioms coordinate_composite
#print axioms relative_square
#print axioms homology_square
end ConstructionTargets.CoefficientChartBallTransport
