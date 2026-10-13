import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
noncomputable section
namespace ConstructionTargets.LinearGraphMeasure
open MeasureTheory Set
open scoped ENNReal
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Ambient (d : ℕ) := WithLp 2 (E d × ℝ)
/-- Formerly a global instance; that made a second `MeasurableSpace` on every
`EuclideanSpace` (a diamond with Mathlib's).  Kept as plain definitions for
consumers that name them; Mathlib's instance is the one in use. -/
def domainMeasurable (d : ℕ) : MeasurableSpace (E d) := borel _
theorem domainBorel (d : ℕ) : @BorelSpace (E d) _ (domainMeasurable d) :=
  @BorelSpace.mk (E d) _ (domainMeasurable d) rfl
instance ambientMeasurable (d : ℕ) : MeasurableSpace (Ambient d) := borel _
instance ambientBorel (d : ℕ) : BorelSpace (Ambient d) := ⟨rfl⟩
variable (d : ℕ) (ell : E d →L[ℝ] ℝ)
def graph : E d →L[ℝ] Ambient d :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (E d) ℝ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ (E d)).prod ell)
theorem graph_value (x : E d) : WithLp.ofLp (graph d ell x) = (x,ell x) := rfl
theorem graph_injective : Function.Injective (graph d ell) := by
  intro x y h
  exact congrArg (fun z => (WithLp.ofLp z).1) h
abbrev range := LinearMap.range (graph d ell).toLinearMap
theorem range_dimension : Module.finrank ℝ (range d ell) = d := by
  rw [LinearMap.finrank_range_of_inj (graph_injective d ell)]
  simp [E]
def rangeIsometry : range d ell ≃ₗᵢ[ℝ] E d :=
  ((stdOrthonormalBasis ℝ (range d ell)).reindex (finCongr (range_dimension d ell))).repr
def rangeMap : E d →ₗ[ℝ] range d ell := (graph d ell).toLinearMap.rangeRestrict
def coordinateMap : E d →ₗ[ℝ] E d := (rangeIsometry d ell).toLinearMap.comp (rangeMap d ell)
theorem coordinate_injective : Function.Injective (coordinateMap d ell) := by
  intro x y h
  have h' := (rangeIsometry d ell).injective h
  exact graph_injective d ell (congrArg Subtype.val h')
def distortion : ℝ := |LinearMap.det (coordinateMap d ell)|
theorem distortion_pos : 0 < distortion d ell := by
  apply abs_pos.mpr
  intro h
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h)
    (LinearMap.ker_eq_bot.mpr (coordinate_injective d ell))
theorem range_measure (s : Set (E d)) :
    Measure.hausdorffMeasure d (rangeMap d ell '' s) =
    ENNReal.ofReal (distortion d ell) * Measure.hausdorffMeasure d s := by
  have h := (rangeIsometry d ell).isometry.hausdorffMeasure_image
    (Or.inl (Nat.cast_nonneg d)) (rangeMap d ell '' s)
  rw [Set.image_image] at h
  rw [← h]
  change Measure.hausdorffMeasure d (coordinateMap d ell '' s) = _
  have hd : Module.finrank ℝ (E d) = d := by simp [E]
  haveI : (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)).IsAddHaarMeasure := by
    simpa only [hd] using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := E d))
  exact MeasureTheory.Measure.addHaar_image_linearMap (Measure.hausdorffMeasure d) (coordinateMap d ell) s

theorem image_measure (s : Set (E d)) :
    Measure.hausdorffMeasure d (graph d ell '' s) =
    ENNReal.ofReal (distortion d ell) * Measure.hausdorffMeasure d s := by
  have h := (isometry_subtype_coe : Isometry (Subtype.val : range d ell → Ambient d)).hausdorffMeasure_image
    (Or.inl (Nat.cast_nonneg d)) (rangeMap d ell '' s)
  rw [Set.image_image] at h
  exact h.trans (range_measure d ell s)
def dimension_two (ell : E 2 →L[ℝ] ℝ) (s : Set (E 2)) := image_measure 2 ell s
def dimension_three (ell : E 3 →L[ℝ] ℝ) (s : Set (E 3)) := image_measure 3 ell s
end ConstructionTargets.LinearGraphMeasure

#print axioms ConstructionTargets.LinearGraphMeasure.graph_value
#print axioms ConstructionTargets.LinearGraphMeasure.graph_injective
#print axioms ConstructionTargets.LinearGraphMeasure.range_dimension
#print axioms ConstructionTargets.LinearGraphMeasure.rangeIsometry
#print axioms ConstructionTargets.LinearGraphMeasure.coordinate_injective
#print axioms ConstructionTargets.LinearGraphMeasure.distortion_pos
#print axioms ConstructionTargets.LinearGraphMeasure.range_measure
#print axioms ConstructionTargets.LinearGraphMeasure.image_measure
#print axioms ConstructionTargets.LinearGraphMeasure.dimension_two
#print axioms ConstructionTargets.LinearGraphMeasure.dimension_three
