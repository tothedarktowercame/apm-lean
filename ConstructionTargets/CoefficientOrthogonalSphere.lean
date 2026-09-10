import ConstructionTargets.CoefficientOrthogonalRadial
noncomputable section
namespace ConstructionTargets.CoefficientOrthogonalSphere
open CategoryTheory CategoryTheory.Limits
open T02A06 T02A06HemisphereExcision T02A06DiskRadialComparison
open CoefficientRadialPair CoefficientOrthogonalRadial
variable (R : Type) [CommRing R]
variable {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))

def sphereAction : C(ambientSphere n, ambientSphere n) where
  toFun x := ⟨euclideanSnoc (Q (euclideanInit x.1)) (sphereHeight n x), by
    rw [Metric.mem_sphere, dist_zero_right]
    have hx : ‖x.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.2
    have he := euclideanInit_norm_sq_add_last x.1
    have hs : ‖euclideanSnoc (Q (euclideanInit x.1)) (sphereHeight n x)‖ ^ 2 = 1 ^ 2 := by
      rw [euclideanSnoc_norm_sq, Q.norm_map]
      simpa only [sphereHeight, hx] using he
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hs⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_euclideanSnoc.comp ((Q.continuous.comp
      (continuous_euclideanInit.comp continuous_subtype_val)).prodMk (continuous_sphereHeight n))

theorem height : sphereHeight n ∘ sphereAction Q = sphereHeight n := by
  funext x
  exact euclideanSnoc_last _ _

theorem north_mapsTo : Set.MapsTo (sphereAction Q) (northPoleComplement n) (northPoleComplement n) := by
  intro x hx
  change sphereHeight n (sphereAction Q x) < 1
  rw [show sphereHeight n (sphereAction Q x) = sphereHeight n x from congrFun (height Q) x]
  exact hx

theorem lower_mapsTo : Set.MapsTo (sphereAction Q) (closedLowerHemisphere n) (closedLowerHemisphere n) := by
  intro x hx
  change sphereHeight n (sphereAction Q x) ≤ 0
  rw [show sphereHeight n (sphereAction Q x) = sphereHeight n x from congrFun (height Q) x]
  exact hx

theorem upper_mapsTo : Set.MapsTo (sphereAction Q) (openUpperHemisphere n) (openUpperHemisphere n) := by
  intro x hx
  change ¬ sphereHeight n (sphereAction Q x) ≤ 0
  rw [show sphereHeight n (sphereAction Q x) = sphereHeight n x from congrFun (height Q) x]
  exact hx

def upperAction : C(openUpperHemisphere n, openUpperHemisphere n) :=
  ⟨fun x => ⟨sphereAction Q x.1, upper_mapsTo Q x.2⟩, by fun_prop⟩

theorem punctured_mapsTo : Set.MapsTo (upperAction Q) (puncturedUpperHemisphere n) (puncturedUpperHemisphere n) := by
  intro x hx
  exact north_mapsTo Q hx

theorem coordinate_square : (upperAction Q).comp (openDiskToOpenUpperMap n) =
    (openDiskToOpenUpperMap n).comp (openAction Q) := by
  ext x : 1
  apply Subtype.ext
  apply Subtype.ext
  change euclideanSnoc (Q (euclideanInit (euclideanSnoc x.1 _)))
    ((euclideanSnoc x.1 _) (Fin.last n)) = euclideanSnoc (Q x.1) _
  rw [euclideanInit_snoc, euclideanSnoc_last]
  change euclideanSnoc (Q x.1) (Real.sqrt (1 - ‖x.1‖ ^ 2)) = euclideanSnoc (Q x.1) (Real.sqrt (1 - ‖Q x.1‖ ^ 2))
  rw [Q.norm_map]

def upperPair := pairMap R _ _ (upperAction Q) (punctured_mapsTo Q)
def spherePair := pairMap R _ _ (sphereAction Q) (north_mapsTo Q)

theorem relative_coordinate_square : CoefficientOrthogonalRadial.openPair R Q ≫
    CoefficientSphereShift.coordinateMap R n = CoefficientSphereShift.coordinateMap R n ≫ upperPair R Q := by
  change pairMap R _ _ _ _ ≫ pairMap R _ _ _ _ = pairMap R _ _ _ _ ≫ pairMap R _ _ _ _
  rw [← CoefficientPairNaturality.pair_comp, ← CoefficientPairNaturality.pair_comp]
  congr 1
  exact (coordinate_square Q).symm

theorem coordinate_naturality (j : ℕ) :
    HomologicalComplex.homologyMap (CoefficientOrthogonalRadial.openPair R Q) j ≫
      (CoefficientSphereShift.coordinateIso R n j).hom =
    (CoefficientSphereShift.coordinateIso R n j).hom ≫ HomologicalComplex.homologyMap (upperPair R Q) j :=
  (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f j) (relative_coordinate_square R Q)).trans
      (HomologicalComplex.homologyMap_comp _ _ j))

def upperInclusion : C(openUpperHemisphere n, ambientSphere n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem upperInclusion_mapsTo : Set.MapsTo (upperInclusion (n := n))
    (puncturedUpperHemisphere n) (northPoleComplement n) := fun _ h => h

theorem excision_geometric_square : (sphereAction Q).comp (upperInclusion (n := n)) =
    (upperInclusion (n := n)).comp (upperAction Q) := by ext x; rfl

theorem excision_actual : CoefficientExcision.excisionMap R (northPoleComplement n)
    (closedLowerHemisphere n) = pairMap R _ _ (upperInclusion (n := n)) upperInclusion_mapsTo := rfl

theorem relative_excision_square : upperPair R Q ≫
    CoefficientExcision.excisionMap R (northPoleComplement n) (closedLowerHemisphere n) =
    CoefficientExcision.excisionMap R (northPoleComplement n) (closedLowerHemisphere n) ≫ spherePair R Q := by
  rw [excision_actual]
  change pairMap R _ _ _ _ ≫ pairMap R _ _ _ _ = pairMap R _ _ _ _ ≫ pairMap R _ _ _ _
  rw [← CoefficientPairNaturality.pair_comp, ← CoefficientPairNaturality.pair_comp]
  congr 1

theorem excision_naturality (j : ℕ) : HomologicalComplex.homologyMap (upperPair R Q) j ≫
    (CoefficientSphereShift.hemisphereIso R n j).hom =
    (CoefficientSphereShift.hemisphereIso R n j).hom ≫ HomologicalComplex.homologyMap (spherePair R Q) j := by
  rw [CoefficientSphereShift.hemisphereIso_hom]
  exact (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f j) (relative_excision_square R Q)).trans
      (HomologicalComplex.homologyMap_comp _ _ j))

theorem coordinate_inverse_naturality (j : ℕ) :
    HomologicalComplex.homologyMap (upperPair R Q) j ≫ (CoefficientSphereShift.coordinateIso R n j).inv =
    (CoefficientSphereShift.coordinateIso R n j).inv ≫ HomologicalComplex.homologyMap (openPair R Q) j := by
  apply (cancel_epi (CoefficientSphereShift.coordinateIso R n j).hom).mp
  have h := congrArg (fun f => f ≫ (CoefficientSphereShift.coordinateIso R n j).inv) (coordinate_naturality R Q j)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using h.symm

theorem excision_inverse_naturality (j : ℕ) :
    HomologicalComplex.homologyMap (spherePair R Q) j ≫ (CoefficientSphereShift.hemisphereIso R n j).inv =
    (CoefficientSphereShift.hemisphereIso R n j).inv ≫ HomologicalComplex.homologyMap (upperPair R Q) j := by
  apply (cancel_epi (CoefficientSphereShift.hemisphereIso R n j).hom).mp
  have h := congrArg (fun f => f ≫ (CoefficientSphereShift.hemisphereIso R n j).inv) (excision_naturality R Q j)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using h.symm

theorem upper_projection (j : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (puncturedUpperHemisphere n))).f j ≫
      (upperPair R Q).f j = (absoluteMap R (upperAction Q)).f j ≫
        (cokernel.π (CoefficientRelativeSmall.subspaceMap R (puncturedUpperHemisphere n))).f j :=
  projection_degree R _ _ _ _ j

theorem sphere_projection (j : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (northPoleComplement n))).f j ≫
      (spherePair R Q).f j = (absoluteMap R (sphereAction Q)).f j ≫
        (cokernel.π (CoefficientRelativeSmall.subspaceMap R (northPoleComplement n))).f j :=
  projection_degree R _ _ _ _ j


private theorem commute_comp {C : Type*} [Category C] {A B D : C}
    {a : A ⟶ A} {b : B ⟶ B} {c : D ⟶ D} {f : A ⟶ B} {g : B ⟶ D}
    (h : a ≫ f = f ≫ b) (h' : b ≫ g = g ≫ c) : a ≫ (f ≫ g) = (f ≫ g) ≫ c := by
  calc
    _ = (a ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = (f ≫ b) ≫ g := congrArg (fun t => t ≫ g) h
    _ = f ≫ (b ≫ g) := Category.assoc _ _ _
    _ = f ≫ (g ≫ c) := congrArg (fun t => f ≫ t) h'
    _ = _ := (Category.assoc _ _ _).symm

def sphereHomologyMap (j : ℕ) := HomologicalComplex.homologyMap (absoluteMap R (sphereAction Q)) j

theorem projection_naturality (j : ℕ) : sphereHomologyMap R Q j ≫
    HomologicalComplex.homologyMap (CoefficientPairSequence.projection R (northPoleComplement n)) j =
    HomologicalComplex.homologyMap (CoefficientPairSequence.projection R (northPoleComplement n)) j ≫
      HomologicalComplex.homologyMap (spherePair R Q) j :=
  (HomologicalComplex.homologyMap_comp _ _ j).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f j)
      (CoefficientRadialPair.projection R _ _ (sphereAction Q) (north_mapsTo Q)).symm).trans
      (HomologicalComplex.homologyMap_comp _ _ j))

theorem sphereToDisk_naturality (j : ℕ) (hj : j ≠ 0) : sphereHomologyMap R Q j ≫
    (CoefficientSphereShift.sphereToDiskIso R n j hj).hom =
    (CoefficientSphereShift.sphereToDiskIso R n j hj).hom ≫
      HomologicalComplex.homologyMap (closedPair R Q) j := by
  rw [CoefficientSphereShift.sphereToDiskIso_hom]
  exact commute_comp (projection_naturality R Q j)
    (commute_comp (excision_inverse_naturality R Q j)
      (commute_comp (coordinate_inverse_naturality R Q j) (radial_inverse_naturality R Q j)))

private theorem commute_inverse {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (a : A ⟶ A) (b : B ⟶ B) (h : a ≫ e.hom = e.hom ≫ b) :
    b ≫ e.inv = e.inv ≫ a := by
  apply (cancel_epi e.hom).mp
  have hh := congrArg (fun f => f ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using hh.symm

theorem sphereToDisk_inverse_naturality (j : ℕ) (hj : j ≠ 0) :
    HomologicalComplex.homologyMap (closedPair R Q) j ≫
      (CoefficientSphereShift.sphereToDiskIso R n j hj).inv =
    (CoefficientSphereShift.sphereToDiskIso R n j hj).inv ≫ sphereHomologyMap R Q j :=
  commute_inverse _ _ _ (sphereToDisk_naturality R Q j hj)

def boundaryHomologyMap (k : ℕ) := (F R k).map (TopCat.ofHom (boundaryAction Q))

theorem boundary_homeomorphism_naturality (k : ℕ) :
    HomologicalComplex.homologyMap (subMap R (closedDiskBoundarySet n) (closedDiskBoundarySet n)
      (closedAction Q) (closed_mapsTo Q)) k ≫
      (F R k).map (TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph n)).hom =
    (F R k).map (TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph n)).hom ≫ boundaryHomologyMap R Q k := by
  change (F R k).map _ ≫ (F R k).map _ = (F R k).map _ ≫ (F R k).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

theorem sphereShift_naturality (k : ℕ) (hk : k ≠ 0) :
    sphereHomologyMap R Q (k+1) ≫ (CoefficientSphereShift.sphereShift R n k hk).hom =
      (CoefficientSphereShift.sphereShift R n k hk).hom ≫ boundaryHomologyMap R Q k := by
  rw [CoefficientSphereShift.sphereShift_hom]
  exact commute_comp (sphereToDisk_naturality R Q (k+1) (by omega))
    (commute_comp (CoefficientPairNaturality.connecting_naturality R
      (closedDiskBoundarySet n) (closedDiskBoundarySet n) (closedAction Q) (closed_mapsTo Q) k).symm
      (boundary_homeomorphism_naturality R Q k))

theorem sphereShift_inverse_naturality (k : ℕ) (hk : k ≠ 0) :
    boundaryHomologyMap R Q k ≫ (CoefficientSphereShift.sphereShift R n k hk).inv =
      (CoefficientSphereShift.sphereShift R n k hk).inv ≫ sphereHomologyMap R Q (k+1) :=
  commute_inverse _ _ _ (sphereShift_naturality R Q k hk)

def integral_comparison (j : ℕ) (hj : j ≠ 0) := sphereToDisk_naturality ℤ Q j hj
def rational_comparison (j : ℕ) (hj : j ≠ 0) := sphereToDisk_naturality ℚ Q j hj
def zero_dimensional (j : ℕ) (hj : j ≠ 0) := sphereToDisk_naturality ℚ
  (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 0))) j hj

def reflection_comparison (j : ℕ) (hj : j ≠ 0) := sphereToDisk_naturality R
  (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin 1))) j hj

theorem reflection_disk_action : closedAction (LinearIsometryEquiv.neg ℝ
    (E := EuclideanSpace ℝ (Fin 1))) = CoefficientBoundaryReflection.reflection := negation_one


/- Coefficients R have universe zero; geometry is over ℝ. All natural-number
dimensions, including zero, are retained. Only homology degrees explicitly
required by the reviewed sphere comparisons are restricted to be positive. -/
#print axioms sphereAction
#print axioms height
#print axioms north_mapsTo
#print axioms lower_mapsTo
#print axioms upper_mapsTo
#print axioms punctured_mapsTo
#print axioms coordinate_square
#print axioms relative_coordinate_square
#print axioms coordinate_naturality
#print axioms excision_geometric_square
#print axioms excision_actual
#print axioms relative_excision_square
#print axioms excision_naturality
#print axioms coordinate_inverse_naturality
#print axioms excision_inverse_naturality
#print axioms upper_projection
#print axioms sphere_projection
#print axioms projection_naturality
#print axioms sphereToDisk_naturality
#print axioms sphereToDisk_inverse_naturality
#print axioms boundary_homeomorphism_naturality
#print axioms sphereShift_naturality
#print axioms sphereShift_inverse_naturality
#print axioms integral_comparison
#print axioms rational_comparison
#print axioms zero_dimensional
#print axioms reflection_comparison
#print axioms reflection_disk_action

end ConstructionTargets.CoefficientOrthogonalSphere
