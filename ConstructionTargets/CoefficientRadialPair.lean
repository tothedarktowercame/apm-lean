import ConstructionTargets.CoefficientContractiblePair
import ConstructionTargets.T02A06DiskRadialComparison
noncomputable section
namespace ConstructionTargets.CoefficientRadialPair
open CategoryTheory CategoryTheory.Limits
open SingularHomologyConcrete SingularExcision
open T02A06DiskRadialComparison T02A06HemisphereExcision
variable (R : Type) [CommRing R]
abbrev chains := CoefficientRelativeSmall.chains R
abbrev F (n : ℕ) := (AlgebraicTopology.singularHomologyFunctor (ModuleCat R) n).obj (ModuleCat.of R R)
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def absoluteMap (f : C(X,Y)) := (chains R).map (TopCat.toSSet.map (TopCat.ofHom f))
def subMap (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :=
  (chains R).map (TopCat.toSSet.map (subspaceMap A B f hf))

theorem square (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :
    CoefficientRelativeSmall.subspaceMap R A ≫ absoluteMap R f =
      subMap R A B f hf ≫ CoefficientRelativeSmall.subspaceMap R B := by
  change (chains R).map _ ≫ (chains R).map _ = (chains R).map _ ≫ (chains R).map _
  simp only [← Functor.map_comp]
  congr 2

def pairMap (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :
    CoefficientRelativeSmall.relativeChains R A ⟶ CoefficientRelativeSmall.relativeChains R B :=
  cokernel.map _ _ (subMap R A B f hf) (absoluteMap R f) (square R A B f hf)

theorem projection (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) :
    cokernel.π (CoefficientRelativeSmall.subspaceMap R A) ≫ pairMap R A B f hf =
      absoluteMap R f ≫ cokernel.π (CoefficientRelativeSmall.subspaceMap R B) := cokernel.π_desc _ _ _

theorem projection_degree (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f A B) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R A)).f n ≫ (pairMap R A B f hf).f n =
      (absoluteMap R f).f n ≫ (cokernel.π (CoefficientRelativeSmall.subspaceMap R B)).f n :=
  congrArg (fun q => q.f n) (projection R A B f hf)

theorem homotopyIso_hom (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv R e n).hom =
      (F R n).map (TopCat.ofHom e.toFun) := rfl

theorem radial_absolute_isIso (m n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (absoluteMap R (halfDiskMap m)) n) := by
  change IsIso ((F R n).map (TopCat.ofHom (halfDiskMap m)))
  rw [← halfDiskHomotopyEquiv_toFun m, ← homotopyIso_hom R (halfDiskHomotopyEquiv m) n]
  infer_instance

theorem radial_subspace_isIso (m n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (subMap R (closedDiskBoundarySet m) (puncturedOpenDiskSet m)
      (halfDiskMap m) (halfDiskMap_mapsTo m)) n) := by
  change IsIso ((F R n).map (subspaceMap _ _ _ _))
  rw [halfDisk_subspaceMap]
  haveI : IsIso ((F R n).map (TopCat.ofHom (halfSphereMap m))) := by
    change IsIso ((F R n).map (TopCat.ofHom (sphereHomotopyEquivPuncturedOpenDisk m).toFun))
    rw [← homotopyIso_hom R (sphereHomotopyEquivPuncturedOpenDisk m) n]
    infer_instance
  let a : TopCat.of (closedDiskBoundarySet m) ⟶ TopCat.of (T02A06.euclideanUnitSphere m) := (TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph m)).hom
  have h := (F R n).map_comp a (TopCat.ofHom (halfSphereMap m))
  let e : TopCat.of (closedDiskBoundarySet m) ≅ TopCat.of (T02A06.euclideanUnitSphere m) := TopCat.isoOfHomeo (closedDiskBoundaryHomeomorph m)
  haveI : IsIso a := (show IsIso e.hom from inferInstance)
  exact h.symm ▸ (inferInstance : IsIso ((F R n).map a ≫ (F R n).map (TopCat.ofHom (halfSphereMap m))))

def radialIso (m n : ℕ) :
    (CoefficientRelativeSmall.relativeChains R (closedDiskBoundarySet m)).homology n ≅
    (CoefficientRelativeSmall.relativeChains R (puncturedOpenDiskSet m)).homology n := by
  letI : Mono (CoefficientRelativeSmall.subspaceMap R (closedDiskBoundarySet m)) := CoefficientRelativeSmall.subspaceMap_mono R _
  letI : Mono (CoefficientRelativeSmall.subspaceMap R (puncturedOpenDiskSet m)) := CoefficientRelativeSmall.subspaceMap_mono R _
  exact CoefficientCokernelComparison.comparisonIso R (CoefficientRelativeSmall.subspaceMap R (closedDiskBoundarySet m))
    (CoefficientRelativeSmall.subspaceMap R (puncturedOpenDiskSet m)) _ _
    (square R _ _ (halfDiskMap m) (halfDiskMap_mapsTo m))
    (radial_subspace_isIso R m) (radial_absolute_isIso R m) n

theorem radialIso_hom (m n : ℕ) :
    (radialIso R m n).hom = HomologicalComplex.homologyMap
      (pairMap R _ _ (halfDiskMap m) (halfDiskMap_mapsTo m)) n := rfl

theorem inverse_left (m n : ℕ) : (radialIso R m n).inv ≫ HomologicalComplex.homologyMap
    (pairMap R _ _ (halfDiskMap m) (halfDiskMap_mapsTo m)) n = 𝟙 _ := (radialIso R m n).inv_hom_id

theorem inverse_right (m n : ℕ) : HomologicalComplex.homologyMap
    (pairMap R _ _ (halfDiskMap m) (halfDiskMap_mapsTo m)) n ≫ (radialIso R m n).inv = 𝟙 _ := (radialIso R m n).hom_inv_id

/-- R and spaces are Type 0; all dimensions and degrees, including zero, are retained. -/
def integral_radial (m n : ℕ) := radialIso ℤ m n
def rational_radial (m n : ℕ) := radialIso ℚ m n
#print axioms square
#print axioms projection_degree
#print axioms radial_absolute_isIso
#print axioms radial_subspace_isIso
#print axioms radialIso_hom
#print axioms inverse_left
#print axioms inverse_right
#print axioms integral_radial
#print axioms rational_radial
end ConstructionTargets.CoefficientRadialPair
