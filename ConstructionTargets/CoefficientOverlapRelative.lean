import ConstructionTargets.CoefficientOverlapPair
noncomputable section
namespace ConstructionTargets.CoefficientOverlapRelative
open CategoryTheory CategoryTheory.Limits
open CoefficientRadialPair CoefficientNeighborhoodLocal CoefficientChartPair CoefficientOverlapPair
variable (R : Type) [CommRing R]
variable (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]

theorem transition_mapsTo (a b x : M) (hx : x ∈ common m a b) :
    Set.MapsTo (homeoMap (transition m a b x))
      (localDeleted (image m a (common m a b) x) 0) (localDeleted (image m b (common m a b) x) 0) := by
  rw [← left_deleted m a b x hx, ← right_deleted m a b x hx]
  exact fun _ hy h => hy ((transition m a b x).injective h)

theorem left_mapsTo (a b x : M) (hx : x ∈ common m a b) :
    Set.MapsTo (leftAmbient m a b x) (localDeleted (image m a (common m a b) x) 0) (deleted x) := by
  intro z hz h
  apply hz
  have he : (left m a b x).symm z = ⟨x,hx⟩ := Subtype.ext h
  have he' : z = left m a b x ⟨x,hx⟩ := ((left m a b x).apply_symm_apply z).symm.trans (congrArg (left m a b x) he)
  exact (congrArg Subtype.val he').trans (left_zero m a b x hx)

theorem right_mapsTo (a b x : M) (hx : x ∈ common m a b) :
    Set.MapsTo (rightAmbient m a b x) (localDeleted (image m b (common m a b) x) 0) (deleted x) := by
  intro z hz h
  apply hz
  have he : (right m a b x).symm z = ⟨x,hx⟩ := Subtype.ext h
  have he' : z = right m a b x ⟨x,hx⟩ := ((right m a b x).apply_symm_apply z).symm.trans (congrArg (right m a b x) he)
  exact (congrArg Subtype.val he').trans (right_zero m a b x hx)

def transitionMap (a b x : M) (hx : x ∈ common m a b) := pairMap R _ _
  (homeoMap (transition m a b x)) (transition_mapsTo m a b x hx)
def leftMap (a b x : M) (hx : x ∈ common m a b) := pairMap R _ _
  (leftAmbient m a b x) (left_mapsTo m a b x hx)
def rightMap (a b x : M) (hx : x ∈ common m a b) := pairMap R _ _
  (rightAmbient m a b x) (right_mapsTo m a b x hx)

theorem relative_square (a b x : M) (hx : x ∈ common m a b) :
    transitionMap R m a b x hx ≫ rightMap R m a b x hx = leftMap R m a b x hx := by
  unfold transitionMap rightMap leftMap
  rw [← CoefficientPairNaturality.pair_comp]
  congr 1
  exact ambient_square m a b x

theorem homology_square (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    HomologicalComplex.homologyMap (transitionMap R m a b x hx) n ≫
      HomologicalComplex.homologyMap (rightMap R m a b x hx) n =
    HomologicalComplex.homologyMap (leftMap R m a b x hx) n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun f => HomologicalComplex.homologyMap f n) (relative_square R m a b x hx))

theorem inverse_mapsTo (a b x : M) (hx : x ∈ common m a b) :
    Set.MapsTo (homeoMap (transition m a b x).symm)
      (localDeleted (image m b (common m a b) x) 0) (localDeleted (image m a (common m a b) x) 0) := by
  rw [← left_deleted m a b x hx, ← right_deleted m a b x hx]
  intro y hy h
  apply hy
  change (transition m a b x).symm y = left m a b x ⟨x,hx⟩ at h
  exact ((transition m a b x).apply_symm_apply y).symm.trans (congrArg (transition m a b x) h)
def inverseMap (a b x : M) (hx : x ∈ common m a b) := pairMap R _ _
  (homeoMap (transition m a b x).symm) (inverse_mapsTo m a b x hx)

theorem inverse_right (a b x : M) (hx : x ∈ common m a b) :
    transitionMap R m a b x hx ≫ inverseMap R m a b x hx = 𝟙 _ := by
  unfold transitionMap inverseMap
  rw [← CoefficientPairNaturality.pair_comp]
  have h : (homeoMap (transition m a b x).symm).comp (homeoMap (transition m a b x)) =
      ContinuousMap.id _ := by apply ContinuousMap.ext; intro y; exact (transition m a b x).symm_apply_apply y
  simpa only [h] using CoefficientPairNaturality.pair_id R (localDeleted (image m a (common m a b) x) 0)
theorem inverse_left (a b x : M) (hx : x ∈ common m a b) :
    inverseMap R m a b x hx ≫ transitionMap R m a b x hx = 𝟙 _ := by
  unfold transitionMap inverseMap
  rw [← CoefficientPairNaturality.pair_comp]
  have h : (homeoMap (transition m a b x)).comp (homeoMap (transition m a b x).symm) =
      ContinuousMap.id _ := by apply ContinuousMap.ext; intro y; exact (transition m a b x).apply_symm_apply y
  simpa only [h] using CoefficientPairNaturality.pair_id R (localDeleted (image m b (common m a b) x) 0)

def relativeIso (a b x : M) (hx : x ∈ common m a b) :
    CoefficientRelativeSmall.relativeChains R (localDeleted (image m a (common m a b) x) 0) ≅
    CoefficientRelativeSmall.relativeChains R (localDeleted (image m b (common m a b) x) 0) where
  hom := transitionMap R m a b x hx
  inv := inverseMap R m a b x hx
  hom_inv_id := inverse_right R m a b x hx
  inv_hom_id := inverse_left R m a b x hx

def homologyIso (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso (relativeIso R m a b x hx)

def integral_square (m : ℕ) (a b x : E m) (hx : x ∈ common m a b) (n : ℕ) := homology_square ℤ m a b x hx n
def rational_square (m : ℕ) (a b x : E m) (hx : x ∈ common m a b) (n : ℕ) := homology_square ℚ m a b x hx n

theorem transition_projection (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted (image m a (common m a b) x) 0))).f n ≫ (transitionMap R m a b x hx).f n =
      (absoluteMap R (homeoMap (transition m a b x))).f n ≫ (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted (image m b (common m a b) x) 0))).f n :=
  CoefficientRadialPair.projection_degree R _ _ _ (transition_mapsTo m a b x hx) n

theorem left_projection (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted (image m a (common m a b) x) 0))).f n ≫ (leftMap R m a b x hx).f n =
      (absoluteMap R (leftAmbient m a b x)).f n ≫ (cokernel.π (CoefficientRelativeSmall.subspaceMap R (deleted x))).f n :=
  CoefficientRadialPair.projection_degree R _ _ _ (left_mapsTo m a b x hx) n

theorem right_projection (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted (image m b (common m a b) x) 0))).f n ≫ (rightMap R m a b x hx).f n =
      (absoluteMap R (rightAmbient m a b x)).f n ≫ (cokernel.π (CoefficientRelativeSmall.subspaceMap R (deleted x))).f n :=
  CoefficientRadialPair.projection_degree R _ _ _ (right_mapsTo m a b x hx) n

theorem inverse_projection (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted (image m b (common m a b) x) 0))).f n ≫ (inverseMap R m a b x hx).f n =
      (absoluteMap R (homeoMap (transition m a b x).symm)).f n ≫ (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted (image m a (common m a b) x) 0))).f n :=
  CoefficientRadialPair.projection_degree R _ _ _ (inverse_mapsTo m a b x hx) n
#print axioms transition_mapsTo
#print axioms left_mapsTo
#print axioms right_mapsTo
#print axioms inverse_mapsTo
#print axioms relative_square
#print axioms homology_square
#print axioms inverse_left
#print axioms inverse_right
#print axioms relativeIso
#print axioms homologyIso
#print axioms transition_projection
#print axioms left_projection
#print axioms right_projection
#print axioms inverse_projection
#print axioms integral_square
#print axioms rational_square
end ConstructionTargets.CoefficientOverlapRelative
