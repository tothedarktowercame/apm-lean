import ConstructionTargets.CoefficientOverlapRelative
noncomputable section
namespace ConstructionTargets.CoefficientOverlapNormalization
open CategoryTheory CategoryTheory.Limits
open CoefficientRadialPair CoefficientNeighborhoodLocal CoefficientChartPair CoefficientOverlapPair
variable (R : Type) [CommRing R]
section General
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
def pairHomeo (e : X ≃ₜ Y) (A : Set X) (B : Set Y) (h : ∀ y, e y ∈ B ↔ y ∈ A) :
    CoefficientRelativeSmall.relativeChains R A ≅ CoefficientRelativeSmall.relativeChains R B where
  hom := pairMap R A B (homeoMap e) (fun y hy => (h y).mpr hy)
  inv := pairMap R B A (homeoMap e.symm) (fun y hy => (h (e.symm y)).mp (by simpa using hy))
  hom_inv_id := by
    rw [← CoefficientPairNaturality.pair_comp]
    have he : (homeoMap e.symm).comp (homeoMap e) = ContinuousMap.id X := by
      apply ContinuousMap.ext; intro y; exact e.symm_apply_apply y
    simpa only [he] using CoefficientPairNaturality.pair_id R A
  inv_hom_id := by
    rw [← CoefficientPairNaturality.pair_comp]
    have he : (homeoMap e).comp (homeoMap e.symm) = ContinuousMap.id Y := by
      apply ContinuousMap.ext; intro y; exact e.apply_symm_apply y
    simpa only [he] using CoefficientPairNaturality.pair_id R B
end General
variable (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
variable (a : M) (U : Set M) (hU : IsOpen U) (h : U ⊆ (chartAt (E m) a).source) (x : M) (hx : x ∈ U)
theorem pointed_zero : (pointed m a U hU h x ⟨x,hx⟩).val = 0 := sub_self _
include hx in
theorem pointed_iff (y : U) :
    pointed m a U hU h x y ∈ localDeleted (image m a U x) 0 ↔ y ∈ localDeleted U x := by
  change (pointed m a U hU h x y).val ≠ 0 ↔ y.val ≠ x
  have he : (pointed m a U hU h x y).val = 0 ↔ y.val = x := by
    constructor
    · intro hy
      have eq : pointed m a U hU h x y = pointed m a U hU h x ⟨x,hx⟩ :=
        Subtype.ext (hy.trans (pointed_zero m a U hU h x hx).symm)
      exact congrArg Subtype.val ((pointed m a U hU h x).injective eq)
    · intro hy
      have eq : y = (⟨x,hx⟩ : U) := Subtype.ext hy
      rw [eq]; exact pointed_zero m a U hU h x hx
  exact not_congr he

def chartPair := pairHomeo R (pointed m a U hU h x) (localDeleted U x)
  (localDeleted (image m a U x) 0) (pointed_iff m a U hU h x hx)
def ambient : C(image m a U x,M) := (inclusion U).comp (homeoMap (pointed m a U hU h x).symm)
include hx in
theorem ambient_mapsTo : Set.MapsTo (ambient m a U hU h x) (localDeleted (image m a U x) 0) (deleted x) := by
  intro y hy
  exact (pointed_iff m a U hU h x hx ((pointed m a U hU h x).symm y)).mp (by simpa using hy)
def ambientMap := pairMap R _ _ (ambient m a U hU h x) (ambient_mapsTo m a U hU h x hx)
theorem factorization : (chartPair R m a U hU h x hx).hom ≫ ambientMap R m a U hU h x hx = inclusionMap R U x := by
  unfold chartPair pairHomeo ambientMap
  dsimp only
  rw [← CoefficientPairNaturality.pair_comp]
  have he : (ambient m a U hU h x).comp (homeoMap (pointed m a U hU h x)) = inclusion U := by
    apply ContinuousMap.ext; intro y
    exact congrArg Subtype.val ((pointed m a U hU h x).symm_apply_apply y)
  unfold inclusionMap
  congr 1
variable [T2Space M]
def ambientIso (n : ℕ) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (chartPair R m a U hU h x hx)).symm ≪≫ inclusionIso R U x hU hx n

theorem ambient_forward (n : ℕ) : (ambientIso R m a U hU h x hx n).hom =
    HomologicalComplex.homologyMap (ambientMap R m a U hU h x hx) n := by
  have hh := congrArg (fun f => HomologicalComplex.homologyMap f n) (factorization R m a U hU h x hx)
  dsimp only at hh
  rw [HomologicalComplex.homologyMap_comp] at hh
  change _ ≫ HomologicalComplex.homologyMap (inclusionMap R U x) n = _
  rw [← hh]
  change HomologicalComplex.homologyMap (chartPair R m a U hU h x hx).inv n ≫
    (HomologicalComplex.homologyMap (chartPair R m a U hU h x hx).hom n ≫
    HomologicalComplex.homologyMap (ambientMap R m a U hU h x hx) n) = _
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id, HomologicalComplex.homologyMap_id, Category.id_comp]

def normalization := (ambientIso R m a U hU h x hx (m+2)).symm ≪≫
  modelNormalization R m (image m a U x) (image_open m a U x)
    ((pointed_zero m a U hU h x hx) ▸ (pointed m a U hU h x ⟨x,hx⟩).property)
def generator := (normalization R m a U hU h x hx).inv.hom (1 : R)
theorem generator_normalization :
    (normalization R m a U hU h x hx).hom.hom (generator R m a U hU h x hx) = 1 :=
  congrArg (fun f => f.hom (1 : R)) (normalization R m a U hU h x hx).inv_hom_id

def leftIso (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :=
  ambientIso R m a (common m a b) (common_open m a b) Set.inter_subset_left x hx n
def rightIso (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :=
  ambientIso R m b (common m a b) (common_open m a b) Set.inter_subset_right x hx n

theorem left_forward (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    (leftIso R m a b x hx n).hom = HomologicalComplex.homologyMap
      (CoefficientOverlapRelative.leftMap R m a b x hx) n := ambient_forward R m a _ _ _ x hx n
theorem right_forward (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    (rightIso R m a b x hx n).hom = HomologicalComplex.homologyMap
      (CoefficientOverlapRelative.rightMap R m a b x hx) n := ambient_forward R m b _ _ _ x hx n

theorem geometric_comparison (a b x : M) (hx : x ∈ common m a b) (n : ℕ) :
    (leftIso R m a b x hx n).hom ≫ (rightIso R m a b x hx n).inv =
      HomologicalComplex.homologyMap (CoefficientOverlapRelative.transitionMap R m a b x hx) n := by
  apply (cancel_mono (rightIso R m a b x hx n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, left_forward, right_forward]
  exact (CoefficientOverlapRelative.homology_square R m a b x hx n).symm

def leftNormalization (a b x : M) (hx : x ∈ common m a b) :=
  (leftIso R m a b x hx (m+2)).symm ≪≫
    modelNormalization R m (image m a (common m a b) x) (image_open m a _ x) (left_image_zero m a b x hx)
def rightNormalization (a b x : M) (hx : x ∈ common m a b) :=
  (rightIso R m a b x hx (m+2)).symm ≪≫
    modelNormalization R m (image m b (common m a b) x) (image_open m b _ x) (right_image_zero m a b x hx)

theorem normalization_comparison (a b x : M) (hx : x ∈ common m a b) :
    (leftNormalization R m a b x hx).inv ≫ (rightNormalization R m a b x hx).hom =
      (modelNormalization R m (image m a (common m a b) x) (image_open m a _ x) (left_image_zero m a b x hx)).inv ≫
      HomologicalComplex.homologyMap (CoefficientOverlapRelative.transitionMap R m a b x hx) (m+2) ≫
      (modelNormalization R m (image m b (common m a b) x) (image_open m b _ x) (right_image_zero m a b x hx)).hom := by
  dsimp only [leftNormalization, rightNormalization, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom]
  rw [Category.assoc, ← Category.assoc (leftIso R m a b x hx (m+2)).hom, geometric_comparison]
  rfl

def integral_comparison (m : ℕ) (a b x : E m) (hx : x ∈ common m a b) := normalization_comparison ℤ m a b x hx
def rational_comparison (m : ℕ) (a b x : E m) (hx : x ∈ common m a b) := normalization_comparison ℚ m a b x hx

theorem ambient_inverse_left (n : ℕ) : (ambientIso R m a U hU h x hx n).inv ≫
    HomologicalComplex.homologyMap (ambientMap R m a U hU h x hx) n = 𝟙 _ := by
  rw [← ambient_forward]; exact (ambientIso R m a U hU h x hx n).inv_hom_id
theorem ambient_inverse_right (n : ℕ) : HomologicalComplex.homologyMap (ambientMap R m a U hU h x hx) n ≫
    (ambientIso R m a U hU h x hx n).inv = 𝟙 _ := by
  rw [← ambient_forward]; exact (ambientIso R m a U hU h x hx n).hom_inv_id

theorem normalization_forward : (normalization R m a U hU h x hx).hom =
    (ambientIso R m a U hU h x hx (m+2)).inv ≫
    (modelNormalization R m (image m a U x) (image_open m a U x)
      ((pointed_zero m a U hU h x hx) ▸ (pointed m a U hU h x ⟨x,hx⟩).property)).hom := rfl
#print axioms pairHomeo
#print axioms pointed_iff
#print axioms chartPair
#print axioms ambient_mapsTo
#print axioms factorization
#print axioms ambientIso
#print axioms ambient_forward
#print axioms ambient_inverse_left
#print axioms ambient_inverse_right
#print axioms normalization
#print axioms normalization_forward
#print axioms generator_normalization
#print axioms left_forward
#print axioms right_forward
#print axioms geometric_comparison
#print axioms normalization_comparison
#print axioms integral_comparison
#print axioms rational_comparison
end ConstructionTargets.CoefficientOverlapNormalization
