import ConstructionTargets.CoefficientChartBallNormalization
noncomputable section
namespace ConstructionTargets.CoefficientSecondChartBoundary
open CategoryTheory CoefficientOverlapPair CoefficientChartBoundaryNeighborhood
open CoefficientChartBallTransport CoefficientRadialPair PuncturedNormedSpaceRadialEquivalence
variable (R : Type) [CommRing R] (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
variable (a b x : M) (hx : x ∈ common m a b) (y : M) (hy : y ∈ common m a b)
  (hp : ‖chartAt (E m) a y - chartAt (E m) a x‖ < r m a b x hx)

def secondMap : C(CoefficientBallBoundaryLift.Ball m (r m a b x hx), E m) :=
  ⟨fun z => chartAt (E m) b (ballMap m a b x hx z).val - chartAt (E m) b y,
    (((chartAt (E m) b).continuousOn.comp_continuous
      (continuous_subtype_val.comp (ballMap m a b x hx).continuous)
      (fun z => (ballMap m a b x hx z).property.2))).sub continuous_const⟩
include hy hp in
theorem second_deleted : Set.MapsTo (secondMap m a b x hx y)
    (CoefficientBallBoundaryLift.boundary m (r m a b x hx))
    (CoefficientModelLocal.puncture (m+2)) := by
  intro z hz he
  apply boundary_deleted m a b x hx y hp hz
  exact (chartAt (E m) b).injOn (ballMap m a b x hx z).property.2 hy.2 (sub_eq_zero.mp he)

def secondRelative := pairMap R _ _ (secondMap m a b x hx y) (second_deleted m a b x hx y hy hp)
def secondBoundary : C(CoefficientBallBoundaryLift.boundary m (r m a b x hx), PuncturedSpace (E m)) :=
  ⟨fun z => ⟨secondMap m a b x hx y z.val, second_deleted m a b x hx y hy hp z.property⟩,
    by fun_prop⟩

def sphereMap : C(UnitSphere (E m), PuncturedSpace (E m)) :=
  (secondBoundary m a b x hx y hy hp).comp
    (CoefficientBallBoundaryLift.sphere m (r m a b x hx) (radius_pos m a b x hx))

theorem sphere_value (z : UnitSphere (E m)) :
    (sphereMap m a b x hx y hy hp z).val = mappedBoundary m a b x hx z -
      (chartAt (E m) b y - chartAt (E m) b x) := by
  change chartAt (E m) b (sourceBoundary m a b x hx z) - chartAt (E m) b y = _
  rw [mapped_formula]
  abel

theorem connecting : CoefficientBallBoundaryLift.lift R m (r m a b x hx) (radius_pos m a b x hx) ≫
    HomologicalComplex.homologyMap (secondRelative R m a b x hx y hy hp) (m+2) ≫
    CoefficientPairSequence.connecting R (CoefficientModelLocal.puncture (m+2)) (m+1) =
    (F R (m+1)).map (TopCat.ofHom (sphereMap m a b x hx y hy hp)) := by
  letI := CoefficientBallBoundaryLift.ballContractible m (r m a b x hx) (radius_pos m a b x hx)
  have nat := CoefficientPairNaturality.connecting_naturality R
    (CoefficientBallBoundaryLift.boundary m (r m a b x hx))
    (CoefficientModelLocal.puncture (m+2)) (secondMap m a b x hx y)
    (second_deleted m a b x hx y hy hp) (m+1)
  have hc := CoefficientContractiblePair.connecting_left R
    (CoefficientBallBoundaryLift.boundary m (r m a b x hx)) (m+1) (by omega)
  have comp := (F R (m+1)).map_comp
    (TopCat.ofHom (CoefficientBallBoundaryLift.sphere m (r m a b x hx) (radius_pos m a b x hx)))
    (TopCat.ofHom (secondBoundary m a b x hx y hy hp))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hn := congrArg (fun f => f.hom ((CoefficientBallBoundaryLift.lift R m
    (r m a b x hx) (radius_pos m a b x hx)).hom z)) nat
  have hl := congrArg (fun f => f.hom (((F R (m+1)).map
    (TopCat.ofHom (CoefficientBallBoundaryLift.sphere m (r m a b x hx) (radius_pos m a b x hx)))).hom z)) hc
  have hh := congrArg (fun f => f.hom z) comp
  exact hn.symm.trans ((congrArg ((F R (m+1)).map
    (TopCat.ofHom (secondBoundary m a b x hx y hy hp))).hom hl).trans hh.symm)
theorem normalized_connecting :
    CoefficientBallBoundaryLift.lift R m (r m a b x hx) (radius_pos m a b x hx) ≫
    HomologicalComplex.homologyMap (secondRelative R m a b x hx y hy hp) (m+2) ≫
    (CoefficientModelLocal.localIso R m).hom =
    (F R (m+1)).map (TopCat.ofHom (sphereMap m a b x hx y hy hp)) ≫
    (F R (m+1)).map (TopCat.ofHom (radialNormalize (E m))) ≫
    (CoefficientSphereAntipodal.normalization R m).hom := by
  rw [CoefficientModelLocal.forward_composite]
  have h := congrArg (fun f => f ≫
    (F R (m+1)).map (TopCat.ofHom (radialNormalize (E m))) ≫
    (CoefficientSphereAntipodal.normalization R m).hom) (connecting R m a b x hx y hy hp)
  simpa only [Category.assoc] using h
#print axioms normalized_connecting
#print axioms second_deleted
#print axioms sphere_value
#print axioms connecting
end ConstructionTargets.CoefficientSecondChartBoundary
