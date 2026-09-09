import ConstructionTargets.SphereCapGraph
open Metric Set MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace ConstructionTargets.SphereCapFiniteMeasure
open SphereCapGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
abbrev plane (e : E) : Submodule ℝ E := (Submodule.span ℝ {e})ᗮ

def domainBallIsometry (e : E) (r : ℝ) :
    capDomain e r ≃ᵢ Metric.closedBall (0 : plane e) r where
  toFun u := ⟨⟨u.val, Submodule.mem_orthogonal_singleton_iff_inner_left.mpr u.property.2⟩,
    by
      change dist (u.val : E) 0 ≤ r
      simpa only [dist_zero_right] using u.property.1⟩
  invFun u := ⟨u.val.val, by
    constructor
    · have h : dist (u.val.val : E) 0 ≤ r := u.property
      simpa only [dist_zero_right] using h
    · exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp u.val.property⟩
  left_inv u := rfl
  right_inv u := rfl
  isometry_toFun := fun _ _ => rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma domain_measure_eq (e : E) (r : ℝ) (d : ℝ) (hd : 0 ≤ d) :
    Measure.hausdorffMeasure d (Set.univ : Set (capDomain e r)) =
      Measure.hausdorffMeasure d (Metric.closedBall (0 : plane e) r) := by
  have h₁ := (domainBallIsometry e r).hausdorffMeasure_image d Set.univ
  have h₂ := (isometry_subtype_coe : Isometry
    (Subtype.val : Metric.closedBall (0 : plane e) r → plane e)).hausdorffMeasure_image
      (Or.inl hd) Set.univ
  simp only [Set.image_univ, EquivLike.range_eq_univ, Subtype.range_coe] at h₁ h₂
  exact h₁.symm.trans h₂.symm

lemma domain_measure_finite (e : E) (r : ℝ) :
    Measure.hausdorffMeasure (Module.finrank ℝ (plane e))
      (Set.univ : Set (capDomain e r)) < ⊤ := by
  rw [domain_measure_eq e r _ (Nat.cast_nonneg _)]
  let L := (stdOrthonormalBasis ℝ (plane e)).repr
  have hm := L.isometry.hausdorffMeasure_image
    (Or.inl (show (0 : ℝ) ≤ Module.finrank ℝ (plane e) by positivity))
    (Metric.closedBall (0 : plane e) r)
  rw [← hm]
  exact ((isCompact_closedBall (0 : plane e) r).image L.continuous).measure_lt_top

lemma cap_measure_finite {r a : ℝ} (ha : 0 < a) (hr : r < 1) (hr0 : 0 ≤ r)
    (har : a^2 ≤ 1-r^2) (e : E) (he : ‖e‖ = 1) :
    Measure.hausdorffMeasure (Module.finrank ℝ (plane e))
      (Set.range (capMap hr hr0 e he)) < ⊤ := by
  apply lt_of_le_of_lt (capMap_hausdorff_bound ha hr hr0 har e he _ (Nat.cast_nonneg _))
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg _) (by simp)
  · exact domain_measure_finite e r

lemma euclidean_cap_measure_finite (d : ℕ) {r a : ℝ}
    (ha : 0 < a) (hr : r < 1) (hr0 : 0 ≤ r) (har : a^2 ≤ 1-r^2)
    (e : EuclideanSpace ℝ (Fin (d+1))) (he : ‖e‖ = 1) :
    Measure.hausdorffMeasure d (Set.range (capMap hr hr0 e he)) < ⊤ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d+1))) = d+1) := ⟨by simp⟩
  have hne : e ≠ 0 := by intro h; simp [h] at he
  have hdim : Module.finrank ℝ (plane e) = d :=
    Submodule.finrank_orthogonal_span_singleton hne
  simpa only [hdim] using cap_measure_finite ha hr hr0 har e he

lemma dimension_two {r a : ℝ} (ha : 0 < a) (hr : r < 1) (hr0 : 0 ≤ r)
    (har : a^2 ≤ 1-r^2) (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1) :
    Measure.hausdorffMeasure 2 (Set.range (capMap hr hr0 e he)) < ⊤ :=
  euclidean_cap_measure_finite 2 ha hr hr0 har e he

lemma dimension_three {r a : ℝ} (ha : 0 < a) (hr : r < 1) (hr0 : 0 ≤ r)
    (har : a^2 ≤ 1-r^2) (e : EuclideanSpace ℝ (Fin 4)) (he : ‖e‖ = 1) :
    Measure.hausdorffMeasure 3 (Set.range (capMap hr hr0 e he)) < ⊤ :=
  euclidean_cap_measure_finite 3 ha hr hr0 har e he

#print axioms euclidean_cap_measure_finite
#print axioms dimension_two
#print axioms dimension_three
#print axioms domainBallIsometry
#print axioms domain_measure_eq
#print axioms domain_measure_finite
#print axioms cap_measure_finite
end ConstructionTargets.SphereCapFiniteMeasure
