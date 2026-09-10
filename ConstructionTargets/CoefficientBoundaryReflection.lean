import ConstructionTargets.CoefficientPairNaturality
import ConstructionTargets.CoefficientSphereEndpoints
noncomputable section
namespace ConstructionTargets.CoefficientBoundaryReflection
open CategoryTheory CategoryTheory.Limits
open T02A06 T02A06DiskRadialComparison T02A06SphereOne SingularHomologyConcrete
open CoefficientSphereEndpoints
variable (R : Type) [CommRing R]

def reflection : C(disk, disk) where
  toFun x := ⟨-x.1, by
    have hx := x.2
    change dist x.1 0 ≤ 1 at hx
    change dist (-x.1) 0 ≤ 1
    simpa only [dist_zero_right, norm_neg] using hx⟩
  continuous_toFun := by fun_prop

theorem reflection_mapsTo : Set.MapsTo reflection boundary boundary := by
  intro x hx
  simpa [boundary, closedDiskBoundarySet, reflection, Metric.mem_sphere, dist_zero_right] using hx

def restricted := SingularExcision.subspaceMap boundary boundary reflection reflection_mapsTo

def boolNot : TopCat.of Bool ⟶ TopCat.of Bool :=
  TopCat.ofHom ⟨Bool.not, continuous_of_discreteTopology⟩

theorem coordinates_reflection : (TopCat.isoOfHomeo boundaryHomeo).inv ≫ restricted ≫
    (TopCat.isoOfHomeo boundaryHomeo).hom = boolNot := by
  ext b : 1
  change boundaryHomeo (restricted (boundaryHomeo.symm b)) = !b
  apply boundaryHomeo.symm.injective
  rw [Homeomorph.symm_apply_apply]
  apply Subtype.ext
  apply Subtype.ext
  ext i
  fin_cases i
  cases b <;> simp [restricted, SingularExcision.subspaceMap, reflection, boundaryHomeo,
    closedDiskOneBoundaryHomeomorphIntervalBoundary, closedDiskOneHomeomorphUnitInterval,
    Homeomorph.subtype, boolHomeomorphIntervalBoundary, boolEquivIntervalBoundary,
    euclideanSnoc] <;> norm_num

def sigmaSwap : (∐ fun _ : Bool => ModuleCat.of R R) ⟶ (∐ fun _ : Bool => ModuleCat.of R R) :=
  Sigma.map' Bool.not (fun _ => 𝟙 _)

def swap : ModuleCat.of R (Bool → R) ⟶ ModuleCat.of R (Bool → R) :=
  ModuleCat.ofHom {
    toFun := fun v b => v (!b)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def boundaryMap := (F R).map restricted

theorem sigma_coordinates : (boundarySigmaIso R).inv ≫ boundaryMap R ≫
    (boundarySigmaIso R).hom = sigmaSwap R := by
  let e : TopCat.of boundary ≅ TopCat.of Bool := TopCat.isoOfHomeo boundaryHomeo
  change (directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Bool).inv ≫
    (F R).map e.inv ≫ (F R).map restricted ≫ (F R).map e.hom ≫
    (directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Bool).hom = _
  have hmap : (F R).map e.inv ≫ (F R).map restricted ≫ (F R).map e.hom = (F R).map boolNot := by
    rw [← Functor.map_comp, ← Functor.map_comp, coordinates_reflection]
  slice_lhs 2 4 => erw [hmap]
  have h := directDiscreteH0Iso_naturality (ModuleCat R) (ModuleCat.of R R) boolNot
  change (directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Bool).inv ≫ (F R).map boolNot =
    sigmaSwap R ≫ (directDiscreteH0Iso (ModuleCat R) (ModuleCat.of R R) Bool).inv at h
  rw [← Category.assoc, h]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem sigmaSwap_coordinates : sigmaSwap R ≫ (boolModuleIso R).hom =
    (boolModuleIso R).hom ≫ swap R := by
  apply Sigma.hom_ext
  intro b
  rw [← Category.assoc, show Sigma.ι (fun _ : Bool => ModuleCat.of R R) b ≫ sigmaSwap R =
    Sigma.ι (fun _ : Bool => ModuleCat.of R R) (!b) by
      simpa only [sigmaSwap, Category.id_comp] using
        (Sigma.ι_comp_map' (f := fun _ : Bool => ModuleCat.of R R) (g := fun _ : Bool => ModuleCat.of R R) (fun b : Bool => !b) (fun _ => 𝟙 (ModuleCat.of R R)) b)]
  dsimp only [boolModuleIso, Iso.trans_hom]
  simp only [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (DirectSum.linearEquivFunOnFintype R Bool (fun _ => R))
    (DirectSum.lof R Bool (fun _ => R) (!b) r) =
    fun c => (DirectSum.linearEquivFunOnFintype R Bool (fun _ => R))
      (DirectSum.lof R Bool (fun _ => R) b r) (!c)
  rw [DirectSum.linearEquivFunOnFintype_lof, DirectSum.linearEquivFunOnFintype_lof]
  funext c
  cases b <;> cases c <;> simp [Pi.single_apply]

theorem boundary_coordinates : boundaryMap R ≫ (boundaryIso R).hom =
    (boundaryIso R).hom ≫ swap R := by
  have hs : boundaryMap R ≫ (boundarySigmaIso R).hom =
      (boundarySigmaIso R).hom ≫ sigmaSwap R := by
    apply (cancel_epi (boundarySigmaIso R).inv).mp
    simpa only [Iso.inv_hom_id_assoc] using sigma_coordinates R
  change boundaryMap R ≫ ((boundarySigmaIso R).hom ≫ (boolModuleIso R).hom) =
    ((boundarySigmaIso R).hom ≫ (boolModuleIso R).hom) ≫ swap R
  rw [← Category.assoc, hs, Category.assoc, sigmaSwap_coordinates, Category.assoc]

def absolute := CoefficientRadialPair.absoluteMap R reflection
def relative := CoefficientRadialPair.pairMap R boundary boundary reflection reflection_mapsTo

theorem projection_degree (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R boundary)).f n ≫ (relative R).f n =
      (absolute R).f n ≫ (cokernel.π (CoefficientRelativeSmall.subspaceMap R boundary)).f n :=
  CoefficientRadialPair.projection_degree R boundary boundary reflection reflection_mapsTo n

theorem inclusion_square : inclusion R ≫ HomologicalComplex.homologyMap (absolute R) 0 =
    boundaryMap R ≫ inclusion R := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f 0)
    (CoefficientRadialPair.square R boundary boundary reflection reflection_mapsTo)
  exact (HomologicalComplex.homologyMap_comp (CoefficientRelativeSmall.subspaceMap R boundary)
    (absolute R) 0).symm.trans (h.trans (HomologicalComplex.homologyMap_comp
      (CoefficientRadialPair.subMap R boundary boundary reflection reflection_mapsTo)
      (CoefficientRelativeSmall.subspaceMap R boundary) 0))

theorem boundary_conjugation : (boundaryIso R).inv ≫ boundaryMap R ≫ (boundaryIso R).hom =
    swap R := by
  rw [boundary_coordinates, Iso.inv_hom_id_assoc]

def integral_boundary := boundary_coordinates ℤ
def rational_boundary := boundary_coordinates ℚ

theorem boundaryMap_actual : boundaryMap R = HomologicalComplex.homologyMap
    (CoefficientRadialPair.subMap R boundary boundary reflection reflection_mapsTo) 0 := rfl

theorem swap_false (v : Bool → R) : (swap R).hom v false = v true := rfl
theorem swap_true (v : Bool → R) : (swap R).hom v true = v false := rfl

/- R is a Type 0 commutative ring. The disk and boundary are actual subtypes.
No nontriviality, field or characteristic assumption is imposed. -/
#print axioms reflection_mapsTo
#print axioms coordinates_reflection
#print axioms sigma_coordinates
#print axioms sigmaSwap_coordinates
#print axioms boundary_coordinates
#print axioms boundaryMap_actual
#print axioms projection_degree
#print axioms inclusion_square
#print axioms boundary_conjugation
#print axioms swap_false
#print axioms swap_true
#print axioms integral_boundary
#print axioms rational_boundary

end ConstructionTargets.CoefficientBoundaryReflection
