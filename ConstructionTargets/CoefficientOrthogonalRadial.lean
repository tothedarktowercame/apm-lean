import ConstructionTargets.CoefficientDiskReflection
noncomputable section
namespace ConstructionTargets.CoefficientOrthogonalRadial
open CategoryTheory CategoryTheory.Limits
open T02A06 T02A06HemisphereExcision T02A06DiskRadialComparison
open CoefficientRadialPair
variable (R : Type) [CommRing R]
variable {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))

def closedAction : C(euclideanClosedDisk n, euclideanClosedDisk n) where
  toFun x := ⟨Q x.1, by
    have h := x.2
    simpa only [Metric.mem_closedBall, dist_zero_right, Q.norm_map] using h⟩
  continuous_toFun := by fun_prop

def openAction : C(euclideanOpenDisk n, euclideanOpenDisk n) where
  toFun x := ⟨Q x.1, by
    have h := x.2
    simpa only [Metric.mem_ball, dist_zero_right, Q.norm_map] using h⟩
  continuous_toFun := by fun_prop

def boundaryAction : C(euclideanUnitSphere n, euclideanUnitSphere n) where
  toFun x := ⟨Q x.1, by
    have h := x.2
    simpa only [Metric.mem_sphere, dist_zero_right, Q.norm_map] using h⟩
  continuous_toFun := by fun_prop

theorem closed_mapsTo : Set.MapsTo (closedAction Q) (closedDiskBoundarySet n) (closedDiskBoundarySet n) := by
  intro x hx
  change x.1 ∈ euclideanUnitSphere n at hx
  change Q x.1 ∈ euclideanUnitSphere n
  simpa only [Metric.mem_sphere, dist_zero_right, Q.norm_map] using hx

theorem open_mapsTo : Set.MapsTo (openAction Q) (puncturedOpenDiskSet n) (puncturedOpenDiskSet n) := by
  intro x hx
  change Q x.1 ≠ 0
  exact fun h => hx (Q.injective (h.trans Q.map_zero.symm))

theorem radial_square : (halfDiskMap n).comp (closedAction Q) = (openAction Q).comp (halfDiskMap n) := by
  ext x : 1
  apply Subtype.ext
  exact (Q.map_smul (1/2 : ℝ) x.1).symm

theorem boundary_square : (boundaryAction Q).comp
    ⟨closedDiskBoundaryHomeomorph n, (closedDiskBoundaryHomeomorph n).continuous⟩ =
    (⟨closedDiskBoundaryHomeomorph n, (closedDiskBoundaryHomeomorph n).continuous⟩ :
      C(closedDiskBoundarySet n, euclideanUnitSphere n)).comp
      ⟨fun x => ⟨closedAction Q x.1, closed_mapsTo Q x.2⟩, by fun_prop⟩ := by
  ext x
  rfl

def closedPair := pairMap R _ _ (closedAction Q) (closed_mapsTo Q)
def openPair := pairMap R _ _ (openAction Q) (open_mapsTo Q)
def radialPair := pairMap R _ _ (halfDiskMap n) (halfDiskMap_mapsTo n)

theorem relative_square : closedPair R Q ≫ radialPair R (n := n) =
    radialPair R (n := n) ≫ openPair R Q := by
  change pairMap R _ _ _ _ ≫ pairMap R _ _ _ _ = pairMap R _ _ _ _ ≫ pairMap R _ _ _ _
  rw [← CoefficientPairNaturality.pair_comp, ← CoefficientPairNaturality.pair_comp]
  congr 1
  exact radial_square Q

theorem radial_naturality (j : ℕ) :
    HomologicalComplex.homologyMap (closedPair R Q) j ≫ (radialIso R n j).hom =
      (radialIso R n j).hom ≫ HomologicalComplex.homologyMap (openPair R Q) j := by
  exact (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f j) (relative_square R Q)).trans
      (HomologicalComplex.homologyMap_comp _ _ j))

theorem radial_inverse_naturality (j : ℕ) :
    HomologicalComplex.homologyMap (openPair R Q) j ≫ (radialIso R n j).inv =
      (radialIso R n j).inv ≫ HomologicalComplex.homologyMap (closedPair R Q) j := by
  apply (cancel_epi (radialIso R n j).hom).mp
  have h := congrArg (fun f => f ≫ (radialIso R n j).inv) (radial_naturality R Q j)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using h.symm

theorem closed_projection (j : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (closedDiskBoundarySet n))).f j ≫
      (closedPair R Q).f j = (absoluteMap R (closedAction Q)).f j ≫
        (cokernel.π (CoefficientRelativeSmall.subspaceMap R (closedDiskBoundarySet n))).f j :=
  projection_degree R _ _ _ _ j

theorem open_projection (j : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (puncturedOpenDiskSet n))).f j ≫
      (openPair R Q).f j = (absoluteMap R (openAction Q)).f j ≫
        (cokernel.π (CoefficientRelativeSmall.subspaceMap R (puncturedOpenDiskSet n))).f j :=
  projection_degree R _ _ _ _ j

theorem negation_one : closedAction (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin 1))) =
    CoefficientBoundaryReflection.reflection := by
  ext x
  rfl

def integral_naturality (j : ℕ) := radial_naturality ℤ Q j
def rational_naturality (j : ℕ) := radial_naturality ℚ Q j

def zero_dimensional (j : ℕ) := radial_naturality ℚ
  (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))) j

/- Geometry is over the real numbers; coefficients use an arbitrary Type 0
commutative ring R. Dimension zero and empty boundary subsets are retained. -/
#print axioms closed_mapsTo
#print axioms open_mapsTo
#print axioms radial_square
#print axioms boundary_square
#print axioms relative_square
#print axioms radial_naturality
#print axioms radial_inverse_naturality
#print axioms closed_projection
#print axioms open_projection
#print axioms negation_one
#print axioms integral_naturality
#print axioms rational_naturality
#print axioms zero_dimensional
end ConstructionTargets.CoefficientOrthogonalRadial
