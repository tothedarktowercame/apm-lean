import ConstructionTargets.CoefficientChartRestriction
noncomputable section
namespace ConstructionTargets.CoefficientChartTransitionUnit
open CategoryTheory
open CoefficientOverlapPair CoefficientOverlapNormalization CoefficientNeighborhoodLocal
variable (R : Type) [CommRing R]
theorem linear_scalar (f : ModuleCat.of R R ⟶ ModuleCat.of R R) (r : R) :
    f.hom r = f.hom 1 * r := by
  have h := f.hom.map_smul r (1 : R)
  simpa only [smul_eq_mul, mul_one, mul_comm] using h

def isoUnit (e : ModuleCat.of R R ≅ ModuleCat.of R R) : Rˣ where
  val := e.hom.hom 1
  inv := e.inv.hom 1
  val_inv := by
    have h := congrArg (fun f => f.hom (1 : R)) e.inv_hom_id
    change e.hom.hom (e.inv.hom 1) = 1 at h
    rw [linear_scalar] at h
    exact h
  inv_val := by
    have h := congrArg (fun f => f.hom (1 : R)) e.hom_inv_id
    change e.inv.hom (e.hom.hom 1) = 1 at h
    rw [linear_scalar] at h
    exact h

theorem isoUnit_action (e : ModuleCat.of R R ≅ ModuleCat.of R R) (r : R) :
    e.hom.hom r = (isoUnit R e : R) * r := linear_scalar R e.hom r

variable (m : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
def chartNormalization (a x : M) (hx : x ∈ (chartAt (E m) a).source) :=
  normalization R m a (chartAt (E m) a).source (chartAt (E m) a).open_source Set.Subset.rfl x hx

theorem left_restriction (a b x : M) (hx : x ∈ common m a b) :
    leftNormalization R m a b x hx = chartNormalization R m a x hx.1 :=
  CoefficientChartRestriction.normalization_restriction R m a (common m a b) _
    (common_open m a b) (chartAt (E m) a).open_source Set.inter_subset_left Set.Subset.rfl Set.inter_subset_left x hx

theorem right_restriction (a b x : M) (hx : x ∈ common m a b) :
    rightNormalization R m a b x hx = chartNormalization R m b x hx.2 :=
  CoefficientChartRestriction.normalization_restriction R m b (common m a b) _
    (common_open m a b) (chartAt (E m) b).open_source Set.inter_subset_right Set.Subset.rfl Set.inter_subset_right x hx

def comparison (a b x : M) (ha : x ∈ (chartAt (E m) a).source)
    (hb : x ∈ (chartAt (E m) b).source) :=
  (chartNormalization R m a x ha).symm ≪≫ chartNormalization R m b x hb

theorem geometric_comparison (a b x : M) (hx : x ∈ common m a b) :
    (comparison R m a b x hx.1 hx.2).hom =
      (modelNormalization R m (image m a (common m a b) x) (image_open m a _ x) (left_image_zero m a b x hx)).inv ≫
      HomologicalComplex.homologyMap (CoefficientOverlapRelative.transitionMap R m a b x hx) (m+2) ≫
      (modelNormalization R m (image m b (common m a b) x) (image_open m b _ x) (right_image_zero m a b x hx)).hom := by
  have h := normalization_comparison R m a b x hx
  rw [left_restriction, right_restriction] at h
  exact h

def transitionUnit (a b x : M) (ha : x ∈ (chartAt (E m) a).source)
    (hb : x ∈ (chartAt (E m) b).source) := isoUnit R (comparison R m a b x ha hb)

theorem scalar_action (a b x : M) (ha : x ∈ (chartAt (E m) a).source)
    (hb : x ∈ (chartAt (E m) b).source) (r : R) :
    (comparison R m a b x ha hb).hom.hom r = (transitionUnit R m a b x ha hb : R) * r :=
  isoUnit_action R _ r

def chartGenerator (a x : M) (ha : x ∈ (chartAt (E m) a).source) :=
  (chartNormalization R m a x ha).inv.hom (1 : R)

theorem generator_change (a b x : M) (ha : x ∈ (chartAt (E m) a).source)
    (hb : x ∈ (chartAt (E m) b).source) :
    chartGenerator R m a x ha = (transitionUnit R m a b x ha hb : R) • chartGenerator R m b x hb := by
  have h := congrArg (fun f => f.hom (chartGenerator R m a x ha))
    (chartNormalization R m b x hb).hom_inv_id
  change (chartNormalization R m b x hb).inv.hom
    ((chartNormalization R m b x hb).hom.hom (chartGenerator R m a x ha)) = _ at h
  change (chartNormalization R m b x hb).inv.hom
    ((chartNormalization R m b x hb).hom.hom (chartGenerator R m a x ha)) = chartGenerator R m a x ha at h
  exact h.symm.trans (by
    simpa only [smul_eq_mul, mul_one] using
      (chartNormalization R m b x hb).inv.hom.map_smul (transitionUnit R m a b x ha hb : R) (1 : R))

theorem comparison_cocycle (a b c x : M) (ha : x ∈ (chartAt (E m) a).source)
    (hb : x ∈ (chartAt (E m) b).source) (hc : x ∈ (chartAt (E m) c).source) :
    comparison R m a b x ha hb ≪≫ comparison R m b c x hb hc = comparison R m a c x ha hc := by
  apply Iso.ext
  simp only [comparison, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

theorem comparison_identity (a x : M) (ha : x ∈ (chartAt (E m) a).source) :
    comparison R m a a x ha ha = Iso.refl _ := by
  apply Iso.ext
  exact (chartNormalization R m a x ha).inv_hom_id

theorem comparison_inverse (a b x : M) (ha : x ∈ (chartAt (E m) a).source)
    (hb : x ∈ (chartAt (E m) b).source) :
    (comparison R m a b x ha hb).symm = comparison R m b a x hb ha := by
  apply Iso.ext
  rfl

theorem unit_cocycle (a b c x : M) (ha : x ∈ (chartAt (E m) a).source)
    (hb : x ∈ (chartAt (E m) b).source) (hc : x ∈ (chartAt (E m) c).source) :
    transitionUnit R m a b x ha hb * transitionUnit R m b c x hb hc = transitionUnit R m a c x ha hc := by
  apply Units.ext
  have h := congrArg (fun e => e.hom.hom (1 : R)) (comparison_cocycle R m a b c x ha hb hc)
  change (comparison R m b c x hb hc).hom.hom ((comparison R m a b x ha hb).hom.hom 1) = _ at h
  rw [linear_scalar] at h
  exact (mul_comm _ _).trans h

theorem unit_identity (a x : M) (ha : x ∈ (chartAt (E m) a).source) :
    transitionUnit R m a a x ha ha = 1 := by
  apply Units.ext
  exact congrArg (fun e => e.hom.hom (1 : R)) (comparison_identity R m a x ha)

theorem unit_inverse (a b x : M) (ha : x ∈ (chartAt (E m) a).source)
    (hb : x ∈ (chartAt (E m) b).source) :
    (transitionUnit R m a b x ha hb)⁻¹ = transitionUnit R m b a x hb ha := by
  apply Units.ext
  rfl

theorem geometric_unit (a b x : M) (hx : x ∈ common m a b) :
    (transitionUnit R m a b x hx.1 hx.2 : R) =
      ((modelNormalization R m (image m a (common m a b) x) (image_open m a _ x) (left_image_zero m a b x hx)).inv ≫
      HomologicalComplex.homologyMap (CoefficientOverlapRelative.transitionMap R m a b x hx) (m+2) ≫
      (modelNormalization R m (image m b (common m a b) x) (image_open m b _ x) (right_image_zero m a b x hx)).hom).hom (1 : R) :=
  congrArg (fun f => f.hom (1 : R)) (geometric_comparison R m a b x hx)

def integral_unit (m : ℕ) (a b x : E m) (hx : x ∈ common m a b) := geometric_unit ℤ m a b x hx
def rational_unit (m : ℕ) (a b x : E m) (hx : x ∈ common m a b) := geometric_unit ℚ m a b x hx
#print axioms isoUnit
#print axioms isoUnit_action
#print axioms left_restriction
#print axioms right_restriction
#print axioms geometric_comparison
#print axioms generator_change
#print axioms comparison_cocycle
#print axioms comparison_identity
#print axioms comparison_inverse
#print axioms unit_cocycle
#print axioms unit_identity
#print axioms unit_inverse
#print axioms geometric_unit
#print axioms integral_unit
#print axioms rational_unit
end ConstructionTargets.CoefficientChartTransitionUnit
