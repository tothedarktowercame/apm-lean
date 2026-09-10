import ConstructionTargets.CoefficientScaledBoundaryNormalization
noncomputable section
namespace ConstructionTargets.CoefficientBallBoundaryLift
open CategoryTheory CategoryTheory.Limits CoefficientRadialPair
open PuncturedNormedSpaceRadialEquivalence
variable (R : Type) [CommRing R] (m : ℕ) (r : ℝ) (hr : 0 < r)
abbrev E := EuclideanSpace ℝ (Fin (m+2))
abbrev Ball := Metric.closedBall (0 : E m) r
def boundary : Set (Ball m r) := {z | ‖z.val‖ = r}
instance ballContractible : ContractibleSpace (Ball m r) :=
  Metric.contractibleSpace_closedBall hr.le

def sphere : C(UnitSphere (E m), boundary m r) :=
  ⟨fun z => ⟨⟨r • z.val, by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := CoefficientScaledBoundaryNormalization.norm_scaled (E m) r hr z
    exact le_of_eq h⟩,
    CoefficientScaledBoundaryNormalization.norm_scaled (E m) r hr z⟩, by fun_prop⟩

def lift :=
  letI := ballContractible m r hr
  (F R (m+1)).map (TopCat.ofHom (sphere m r hr)) ≫
  (CoefficientContractiblePair.contractibleConnectingIso R (boundary m r) (m+1) (by omega)).inv

variable (p : E m) (hp : ‖p‖ < r)
def recenter : C(Ball m r, E m) := ⟨fun z => z.val-p, by fun_prop⟩
include hp in
theorem recenter_mapsTo : Set.MapsTo (recenter m r p) (boundary m r)
    (CoefficientModelLocal.puncture (m+2)) := by
  intro z hz he
  have hzp : z.val = p := sub_eq_zero.mp he
  have hnorm : ‖z.val‖ = r := hz
  rw [hzp] at hnorm
  exact (ne_of_lt hp) hnorm

def relativeMap := pairMap R (boundary m r) (CoefficientModelLocal.puncture (m+2))
  (recenter m r p) (recenter_mapsTo m r p hp)
def boundaryMap : C(boundary m r, PuncturedSpace (E m)) :=
  ⟨fun z => ⟨z.val.val-p, recenter_mapsTo m r p hp z.property⟩, by fun_prop⟩

theorem boundary_composite : (boundaryMap m r p hp).comp (sphere m r hr) =
    CoefficientScaledBoundaryNormalization.recentered (E m) r hr p hp := by
  apply ContinuousMap.ext
  intro z
  rfl

theorem connecting_equation : lift R m r hr ≫
    HomologicalComplex.homologyMap (relativeMap R m r p hp) (m+2) ≫
    CoefficientPairSequence.connecting R (CoefficientModelLocal.puncture (m+2)) (m+1) =
    (F R (m+1)).map (TopCat.ofHom
      (CoefficientScaledBoundaryNormalization.recentered (E m) r hr p hp)) := by
  letI := ballContractible m r hr
  have nat := CoefficientPairNaturality.connecting_naturality R (boundary m r)
    (CoefficientModelLocal.puncture (m+2)) (recenter m r p)
    (recenter_mapsTo m r p hp) (m+1)
  have comp : (F R (m+1)).map (TopCat.ofHom (sphere m r hr)) ≫
    (F R (m+1)).map (TopCat.ofHom (boundaryMap m r p hp)) =
    (F R (m+1)).map (TopCat.ofHom
      (CoefficientScaledBoundaryNormalization.recentered (E m) r hr p hp)) := by
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg (fun f => (F R (m+1)).map (TopCat.ofHom f))
      (boundary_composite m r hr p hp)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hn := congrArg (fun f => f.hom ((lift R m r hr).hom z)) nat
  have hc := congrArg (fun f => f.hom
    (((F R (m+1)).map (TopCat.ofHom (sphere m r hr))).hom z))
    (CoefficientContractiblePair.connecting_left R (boundary m r) (m+1) (by omega))
  have hb := congrArg (fun f => f.hom z) comp
  change _ = _ at hn hc hb
  exact hn.symm.trans ((congrArg
    ((F R (m+1)).map (TopCat.ofHom (boundaryMap m r p hp))).hom hc).trans hb)

theorem normalization : lift R m r hr ≫
    HomologicalComplex.homologyMap (relativeMap R m r p hp) (m+2) ≫
    (CoefficientModelLocal.localIso R m).hom =
    (CoefficientSphereAntipodal.normalization R m).hom := by
  have h := congrArg (fun f => f ≫
    (F R (m+1)).map (TopCat.ofHom (radialNormalize (E m))))
    (connecting_equation R m r hr p hp)
  have h' := congrArg (fun f => f ≫ (CoefficientSphereAntipodal.normalization R m).hom) h
  simpa only [Category.assoc, CoefficientModelLocal.forward_composite,
    CoefficientScaledBoundaryNormalization.inverse_right, Category.id_comp] using h'

theorem projection (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (boundary m r))).f n ≫
      (relativeMap R m r p hp).f n =
    (absoluteMap R (recenter m r p)).f n ≫
      (cokernel.π (CoefficientRelativeSmall.subspaceMap R
        (CoefficientModelLocal.puncture (m+2)))).f n :=
  CoefficientRadialPair.projection_degree R (boundary m r)
    (CoefficientModelLocal.puncture (m+2)) (recenter m r p)
    (recenter_mapsTo m r p hp) n

def integral_example := normalization ℤ m r hr p hp
def rational_example := normalization ℚ m r hr p hp
end ConstructionTargets.CoefficientBallBoundaryLift

#print axioms ConstructionTargets.CoefficientBallBoundaryLift.ballContractible
#print axioms ConstructionTargets.CoefficientBallBoundaryLift.sphere
#print axioms ConstructionTargets.CoefficientBallBoundaryLift.lift
#print axioms ConstructionTargets.CoefficientBallBoundaryLift.recenter_mapsTo
#print axioms ConstructionTargets.CoefficientBallBoundaryLift.boundary_composite
#print axioms ConstructionTargets.CoefficientBallBoundaryLift.connecting_equation
#print axioms ConstructionTargets.CoefficientBallBoundaryLift.normalization
#print axioms ConstructionTargets.CoefficientBallBoundaryLift.projection
#print axioms ConstructionTargets.CoefficientBallBoundaryLift.integral_example
#print axioms ConstructionTargets.CoefficientBallBoundaryLift.rational_example
