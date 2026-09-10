import ConstructionTargets.CoefficientChartTransitionUnit
import ConstructionTargets.CoefficientDistinguishedNormalization
noncomputable section
namespace ConstructionTargets.CoefficientOverlapTransition
open CategoryTheory CategoryTheory.Limits
open CoefficientOverlapPair CoefficientOverlapNormalization CoefficientNeighborhoodLocal CoefficientChartPair CoefficientRadialPair
variable (R : Type) [CommRing R] (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
variable (U : Set M) (hU : IsOpen U) (a b c x : M)
  (ha : U ⊆ (chartAt (E m) a).source) (hb : U ⊆ (chartAt (E m) b).source)
  (hc : U ⊆ (chartAt (E m) c).source) (hx : x ∈ U)
def coordinateTransition := (pointed m a U hU ha x).symm.trans (pointed m b U hU hb x)
theorem coordinate_composition :
    (homeoMap (coordinateTransition m U hU b c x hb hc)).comp
      (homeoMap (coordinateTransition m U hU a b x ha hb)) =
      homeoMap (coordinateTransition m U hU a c x ha hc) := by
  apply ContinuousMap.ext; intro y
  exact congrArg (pointed m c U hU hc x) ((pointed m b U hU hb x).symm_apply_apply _)
include hx in
theorem deleted_iff (y : image m a U x) :
    coordinateTransition m U hU a b x ha hb y ∈ localDeleted (image m b U x) 0 ↔
      y ∈ localDeleted (image m a U x) 0 := by
  change pointed m b U hU hb x ((pointed m a U hU ha x).symm y) ∈ _ ↔ _
  rw [pointed_iff m b U hU hb x hx]
  exact (pointed_iff m a U hU ha x hx ((pointed m a U hU ha x).symm y)).symm.trans (by simp)
def relativeTransition := pairMap R (localDeleted (image m a U x) 0) (localDeleted (image m b U x) 0)
  (homeoMap (coordinateTransition m U hU a b x ha hb)) (fun y hy => (deleted_iff m U hU a b x ha hb hx y).mpr hy)
theorem relative_composition :
    relativeTransition R m U hU a b x ha hb hx ≫ relativeTransition R m U hU b c x hb hc hx =
      relativeTransition R m U hU a c x ha hc hx := by
  unfold relativeTransition
  rw [← CoefficientPairNaturality.pair_comp]
  congr 1
  exact coordinate_composition m U hU a b c x ha hb hc
theorem homology_composition (n : ℕ) :
    HomologicalComplex.homologyMap (relativeTransition R m U hU a b x ha hb hx) n ≫
      HomologicalComplex.homologyMap (relativeTransition R m U hU b c x hb hc hx) n =
      HomologicalComplex.homologyMap (relativeTransition R m U hU a c x ha hc hx) n := by
  rw [← HomologicalComplex.homologyMap_comp, relative_composition]
theorem relative_identity : relativeTransition R m U hU a a x ha ha hx = 𝟙 _ := by
  unfold relativeTransition
  have he : homeoMap (coordinateTransition m U hU a a x ha ha) = ContinuousMap.id _ := by
    apply ContinuousMap.ext; intro y
    exact (pointed m a U hU ha x).apply_symm_apply y
  simpa only [he] using CoefficientPairNaturality.pair_id R (localDeleted (image m a U x) 0)
theorem relative_inverse : relativeTransition R m U hU a b x ha hb hx ≫
    relativeTransition R m U hU b a x hb ha hx = 𝟙 _ := by
  rw [relative_composition, relative_identity]
theorem projection (n : ℕ) :
    (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted (image m a U x) 0))).f n ≫
      (relativeTransition R m U hU a b x ha hb hx).f n =
    (absoluteMap R (homeoMap (coordinateTransition m U hU a b x ha hb))).f n ≫
      (cokernel.π (CoefficientRelativeSmall.subspaceMap R (localDeleted (image m b U x) 0))).f n :=
  CoefficientRadialPair.projection_degree R _ _ _ _ n

theorem ambient_square : relativeTransition R m U hU a b x ha hb hx ≫
    ambientMap R m b U hU hb x hx = ambientMap R m a U hU ha x hx := by
  unfold relativeTransition ambientMap
  rw [← CoefficientPairNaturality.pair_comp]
  congr 1
  apply ContinuousMap.ext; intro y
  exact congrArg Subtype.val ((pointed m b U hU hb x).symm_apply_apply _)
theorem ambient_homology_square (n : ℕ) :
    HomologicalComplex.homologyMap (relativeTransition R m U hU a b x ha hb hx) n ≫
      HomologicalComplex.homologyMap (ambientMap R m b U hU hb x hx) n =
      HomologicalComplex.homologyMap (ambientMap R m a U hU ha x hx) n := by
  rw [← HomologicalComplex.homologyMap_comp, ambient_square]

theorem coordinate_formula (y : image m a U x) :
    (coordinateTransition m U hU a b x ha hb y).val =
      chartAt (E m) b ((chartAt (E m) a).symm (y.val + chartAt (E m) a x)) - chartAt (E m) b x := rfl

theorem common_transition (a b x : M) (hx : x ∈ common m a b) :
    relativeTransition R m (common m a b) (common_open m a b) a b x
      Set.inter_subset_left Set.inter_subset_right hx = CoefficientOverlapRelative.transitionMap R m a b x hx := rfl

def triple (a b c : M) := common m a b ∩ (chartAt (E m) c).source
theorem triple_open (a b c : M) : IsOpen (triple m a b c) :=
  (common_open m a b).inter (chartAt (E m) c).open_source

theorem triple_composition (a b c x : M) (hx : x ∈ triple m a b c) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeTransition R m (triple m a b c) (triple_open m a b c)
      a b x (fun _ h => h.1.1) (fun _ h => h.1.2) hx) n ≫
    HomologicalComplex.homologyMap (relativeTransition R m (triple m a b c) (triple_open m a b c)
      b c x (fun _ h => h.1.2) (fun _ h => h.2) hx) n =
    HomologicalComplex.homologyMap (relativeTransition R m (triple m a b c) (triple_open m a b c)
      a c x (fun _ h => h.1.1) (fun _ h => h.2) hx) n := homology_composition R m _ _ a b c x _ _ _ hx n
variable [T2Space M]
def modelCoordinates := modelNormalization R m (image m a U x) (image_open m a U x)
  ((pointed_zero m a U hU ha x hx) ▸ (pointed m a U hU ha x ⟨x,hx⟩).property)
def normalizedTransition := (modelCoordinates R m U hU a x ha hx).inv ≫
  HomologicalComplex.homologyMap (relativeTransition R m U hU a b x ha hb hx) (m+2) ≫
  (modelCoordinates R m U hU b x hb hx).hom

omit [T2Space M] in
theorem normalized_composition :
    normalizedTransition R m U hU a b x ha hb hx ≫ normalizedTransition R m U hU b c x hb hc hx =
      normalizedTransition R m U hU a c x ha hc hx := by
  unfold normalizedTransition
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (HomologicalComplex.homologyMap _ _), homology_composition]

omit [T2Space M] in
theorem normalized_identity : normalizedTransition R m U hU a a x ha ha hx = 𝟙 _ := by
  unfold normalizedTransition
  rw [relative_identity, HomologicalComplex.homologyMap_id, Category.id_comp, Iso.inv_hom_id]
omit [T2Space M] in
theorem normalized_inverse : normalizedTransition R m U hU a b x ha hb hx ≫
    normalizedTransition R m U hU b a x hb ha hx = 𝟙 _ := by
  rw [normalized_composition, normalized_identity]

theorem ambient_comparison (n : ℕ) :
    (ambientIso R m a U hU ha x hx n).hom ≫ (ambientIso R m b U hU hb x hx n).inv =
      HomologicalComplex.homologyMap (relativeTransition R m U hU a b x ha hb hx) n := by
  apply (cancel_mono (ambientIso R m b U hU hb x hx n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, ambient_forward, ambient_forward]
  exact (ambient_homology_square R m U hU a b x ha hb hx n).symm

theorem normalization_comparison :
    (normalization R m a U hU ha x hx).inv ≫ (normalization R m b U hU hb x hx).hom =
      normalizedTransition R m U hU a b x ha hb hx := by
  dsimp only [normalization, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom]
  rw [Category.assoc, ← Category.assoc (ambientIso R m a U hU ha x hx (m+2)).hom, ambient_comparison]
  rfl

theorem chart_comparison :
    (CoefficientChartTransitionUnit.comparison R m a b x (ha hx) (hb hx)).hom =
      normalizedTransition R m U hU a b x ha hb hx := by
  have h := normalization_comparison R m U hU a b x ha hb hx
  rw [CoefficientChartRestriction.normalization_restriction R m a U _ hU
    (chartAt (E m) a).open_source ha Set.Subset.rfl ha x hx,
    CoefficientChartRestriction.normalization_restriction R m b U _ hU
    (chartAt (E m) b).open_source hb Set.Subset.rfl hb x hx] at h
  exact h

include hU in
theorem geometric_unit_cocycle :
    CoefficientChartTransitionUnit.transitionUnit R m a b x (ha hx) (hb hx) *
      CoefficientChartTransitionUnit.transitionUnit R m b c x (hb hx) (hc hx) =
      CoefficientChartTransitionUnit.transitionUnit R m a c x (ha hx) (hc hx) := by
  apply Units.ext
  have h := normalized_composition R m U hU a b c x ha hb hc hx
  rw [← chart_comparison, ← chart_comparison, ← chart_comparison] at h
  have hv := congrArg (fun f => f.hom (1 : R)) h
  change (CoefficientChartTransitionUnit.comparison R m b c x (hb hx) (hc hx)).hom.hom
    ((CoefficientChartTransitionUnit.comparison R m a b x (ha hx) (hb hx)).hom.hom 1) = _ at hv
  rw [CoefficientChartTransitionUnit.linear_scalar] at hv
  exact (mul_comm _ _).trans hv

include hU in
theorem geometric_unit_identity :
    CoefficientChartTransitionUnit.transitionUnit R m a a x (ha hx) (ha hx) = 1 := by
  apply Units.ext
  have h := normalized_identity R m U hU a x ha hx
  rw [← chart_comparison] at h
  exact congrArg (fun f => f.hom (1 : R)) h
include hU in
theorem geometric_unit_inverse :
    (CoefficientChartTransitionUnit.transitionUnit R m a b x (ha hx) (hb hx))⁻¹ =
      CoefficientChartTransitionUnit.transitionUnit R m b a x (hb hx) (ha hx) := by
  have h := geometric_unit_cocycle R m U hU a b a x ha hb ha hx
  rw [geometric_unit_identity R m U hU a x ha hx] at h
  exact (inv_eq_of_mul_eq_one_right h)

theorem distinguished (x : M) :
    CoefficientChartTransitionUnit.chartNormalization R m x x (mem_chart_source (E m) x) =
      CoefficientChartLocal.localIso R m x := CoefficientDistinguishedNormalization.distinguished R m x
theorem normalized_scalar (r : R) :
    (normalizedTransition R m U hU a b x ha hb hx).hom r =
      (CoefficientChartTransitionUnit.transitionUnit R m a b x (ha hx) (hb hx) : R) * r := by
  rw [← chart_comparison]
  exact CoefficientChartTransitionUnit.scalar_action R m a b x (ha hx) (hb hx) r

theorem geometric_generator_change :
    CoefficientChartTransitionUnit.chartGenerator R m a x (ha hx) =
      (normalizedTransition R m U hU a b x ha hb hx).hom (1 : R) •
      CoefficientChartTransitionUnit.chartGenerator R m b x (hb hx) := by
  rw [← chart_comparison]
  exact CoefficientChartTransitionUnit.generator_change R m a b x (ha hx) (hb hx)

theorem triple_unit_cocycle (a b c x : M) (hx : x ∈ triple m a b c) :
    CoefficientChartTransitionUnit.transitionUnit R m a b x hx.1.1 hx.1.2 *
      CoefficientChartTransitionUnit.transitionUnit R m b c x hx.1.2 hx.2 =
      CoefficientChartTransitionUnit.transitionUnit R m a c x hx.1.1 hx.2 :=
  geometric_unit_cocycle R m (triple m a b c) (triple_open m a b c) a b c x
    (fun _ h => h.1.1) (fun _ h => h.1.2) (fun _ h => h.2) hx

def integral_triple (m : ℕ) (a b c x : E m) (hx : x ∈ triple m a b c) := triple_unit_cocycle ℤ m a b c x hx
def rational_triple (m : ℕ) (a b c x : E m) (hx : x ∈ triple m a b c) := triple_unit_cocycle ℚ m a b c x hx

def integral_recovery (m : ℕ) (x : E m) := distinguished ℤ m x
def rational_recovery (m : ℕ) (x : E m) := distinguished ℚ m x
#print axioms coordinate_composition
#print axioms coordinate_formula
#print axioms deleted_iff
#print axioms relative_composition
#print axioms homology_composition
#print axioms relative_identity
#print axioms relative_inverse
#print axioms projection
#print axioms common_transition
#print axioms ambient_square
#print axioms ambient_homology_square
#print axioms triple_open
#print axioms triple_composition
#print axioms normalized_composition
#print axioms ambient_comparison
#print axioms normalization_comparison
#print axioms chart_comparison
#print axioms geometric_unit_cocycle
#print axioms normalized_identity
#print axioms normalized_inverse
#print axioms geometric_unit_identity
#print axioms geometric_unit_inverse
#print axioms distinguished
#print axioms normalized_scalar
#print axioms geometric_generator_change
#print axioms triple_unit_cocycle
#print axioms integral_triple
#print axioms rational_triple
#print axioms integral_recovery
#print axioms rational_recovery
#print axioms CoefficientOverlapPair.image_open
#print axioms CoefficientOverlapPair.left_image_zero
#print axioms CoefficientOverlapPair.right_image_zero
#print axioms CoefficientOverlapRelative.inverse_projection
#print axioms CoefficientChartTransitionUnit.isoUnit
#print axioms CoefficientChartTransitionUnit.unit_identity
#print axioms CoefficientChartTransitionUnit.unit_inverse
end ConstructionTargets.CoefficientOverlapTransition
